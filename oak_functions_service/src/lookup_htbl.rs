//
// Copyright 2024 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

// This is a key/value hash table optimized for large numbers of small k/v pairs.  We assume we
// bust out of on-chip cache, so speed is limited by cache misses, not the actual operations such
// as hashing and bit manipulation.
//
// The k/v pairs are loaded before any are read, and once they are loaded cannot be modified.  We
// take advantage of these restrictions to build a hash table with far less memory overhead per k/v
// pair (20 bytes vs ~128 bytes for hashbrown<Vec<u8>, Vec<u8>>), and similar speed k/v lookups
// (~90ns on manual tests).  For small average k/v pairs, of around 64 bytes total, this hash table
// is about 2.5X more memory efficient.

use alloc::{vec, vec::Vec};
use bytes::Bytes;

// To save memory, we use 5 byte array index values instead of 8 bytes.  This saves 12 bytes per
// k/v pair.  It is referred to as u40 below.
const INDEX_SIZE: usize = 5;
// Size of an entry in the hash table.
const ENTRY_SIZE: usize = INDEX_SIZE + 1;

// The hash table consists of 2 vectors.  The first is a table of "entries", which is a packed
// array of entries with the following layout:
//
//    hash_byte: u8
//    data_index: u40  // A 5-byte index, so we support up to 1TiB of data.
//
// This is a "swiss" table meaning that instead of the usual "buckets" of entries, the entries are
// collapsed into the hash table itself.  By adding a 1-byte hash, we can eliminate over 99.5% of
// key comparisons to the wrong keys.  This is important for speed because comparing keys causes a
// page fault usually, while comparing thie 1-byte hash is usually an L1 cache hit.  The number of
// cache misses per lookup should be close to 2 for values found in the table, and 1 for values not
// in the table.
//
// The second table contains fixed k/v entries in the following format:
//
//     key_len: u40
//     key: [u8]
//     value_len: u40
//     value: [u8]
//
// Another memory savings comes from using a swiss table with exactly a 60% load factor.  Swiss
// tables require a significant portion of the table be empty, and normally as the table grows,
// they dynamically double the size.  At least when using the alloc crate, this resize causes a new
// table to be allocated at 2X the size, data is copied from the old table to the new, and the old
// table is freed.  This results in a 3X expansion in memory usage vs the prior array size.  In
// contrast, this scheme has only 40% of the table empty and is never resized.
//
// This reduce scheme currently limits the number of entries to 2^32.
#[derive(Default)]
pub struct LookupHtbl {
    table: Vec<u8>,
    data: Vec<u8>,
    num_entries: usize,
    used_data: usize,
    used_entries: usize,
    reserved: bool,
}

enum LookupResult {
    Found(usize),        // (data_index: u40)
    NotFound(usize, u8), // (table_index: u40, hash_byte: u8)
}

impl LookupHtbl {
    pub fn new() -> LookupHtbl {
        LookupHtbl {
            table: vec![0u8; 0],
            data: vec![0u8; 0],
            num_entries: 0usize,
            used_data: 0usize,
            used_entries: 0usize,
            reserved: false,
        }
    }

    // `additional_data` must be at least as large as the sum of all key and value data.  `num_keys`
    // must be exactly the number of keys that will be loaded.  Reurns false if OOM.
    pub fn try_reserve(&mut self, num_entries: u64, additional_data: u64) -> anyhow::Result<()> {
        // Use a load factor of exactly 60%, rather than then next power of 2 larger than 60% load
        // factor.  This requires we call reduce to convert a hash to a table index rather than
        // simply masking off the upper bits, but the memory savings is worth it.
        let num_entries = (5 * num_entries / 3) as usize;
        self.num_entries = num_entries;
        self.table = vec![0u8; ENTRY_SIZE * num_entries];
        // Allocate 1 extra byte, so the 0 index can be used as NULL.
        self.data = vec![0u8; (additional_data as usize + 3 * INDEX_SIZE *
            (num_entries as usize) + 1) as usize];
        self.used_data = 1usize;
        self.used_entries = 0usize;
        self.reserved = true;
        Ok(())
    }

    // Lookup the key/value pair.  If found, return LookupFound(data_index).  Otherwise, return the
    // table index that contains 0 which can be used during insert, as NotFound(table_index).
    fn lookup(&self, key: &[u8]) -> LookupResult {
        let key_hash: u64 = hash(key);
        let key_hash_byte = key_hash as u8;
        let mut table_index = ENTRY_SIZE * reduce(key_hash as u32, self.num_entries as u32);
        let mut data_index: usize;
        loop {
            // We try to load only the hash byte to save time.  Once we have a matching hash byte,
            // the loop ends and we compare keys.
            let mut entry_hash_byte = self.table[table_index];
            while entry_hash_byte != key_hash_byte {
                if entry_hash_byte == 0 {
                    data_index = read_index(&self.table, table_index + 1);
                    if data_index == 0usize {
                        return LookupResult::NotFound(table_index, key_hash_byte);
                    }
                }
                table_index += ENTRY_SIZE;
                if table_index == self.table.len() {
                    table_index = 0;
                }
                entry_hash_byte = self.table[table_index];
            }
            data_index = read_index(&self.table, table_index + 1);
            if data_index == 0usize {
                // This only happens if the key hash byte is 0.
                return LookupResult::NotFound(table_index, key_hash_byte);
            }
            let key_len = read_index(&self.data, data_index);
            let key_index = data_index + INDEX_SIZE;
            let entry_key: &[u8] = &self.data[key_index..key_index + key_len];
            if entry_key == key {
                return LookupResult::Found(data_index);
            }
            table_index += ENTRY_SIZE;
            if table_index == self.table.len() {
                table_index = 0;
            }
        }
    }

    pub fn contains_key(&self, key: &[u8]) -> bool {
        match self.lookup(key) {
            LookupResult::Found(_) => true,
            _ => false,
        }
    }

    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        let result = self.lookup(key);
        match result {
            LookupResult::Found(data_index) => {
                let key_len = read_index(&self.data, data_index);
                let value_len_index = data_index + INDEX_SIZE + key_len;
                let value_len = read_index(&self.data, value_len_index);
                let value_index = value_len_index + INDEX_SIZE;
                Some(&self.data[value_index..value_index + value_len])
            }
            LookupResult::NotFound(_, _) => None,
        }
    }

    // Insert a k/v pair into the table.  Panics if it is already in the table.
    pub fn insert(&mut self, key: &[u8], value: &[u8]) {
        let result = self.lookup(key);
        match result {
            LookupResult::Found(_) => panic!("Key already in table"),
            LookupResult::NotFound(table_index, hash_byte) => {
                let data_index = self.new_data(key, value);
                self.table[table_index] = hash_byte;
                write_index(&mut self.table, table_index + 1, data_index);
                self.used_entries += 1;
            }
        }
    }

    pub fn new_data(&mut self, key: &[u8], value: &[u8]) -> usize {
        let index = self.used_data;
        write_index(&mut self.data, index, key.len());
        let key_index = index + INDEX_SIZE;
        self.data[key_index..key_index + key.len()].copy_from_slice(key);
        let value_len_index = key_index + key.len();
        write_index(&mut self.data, value_len_index, value.len());
        let value_index = value_len_index + INDEX_SIZE;
        self.data[value_index..value_index + value.len()].copy_from_slice(value);
        self.used_data = value_index + value.len();
        index
    }

    pub fn extend<T: IntoIterator<Item = (Bytes, Bytes)>>(&mut self, new_data: T) {
        assert!(self.reserved);
        for (key, value) in new_data {
            self.insert(&key, &value);
        }
    }

    pub fn len(&self) -> usize {
        self.used_entries
    }

    pub fn is_empty(&self) -> bool {
        return self.used_entries == 0
    }

     pub fn iter(&self) -> LookupHtblIter {
        LookupHtblIter {
            htbl: &self,
            table_index: 0,
        }
    }
}

pub struct LookupHtblIter<'a> {
    htbl: &'a LookupHtbl,
    table_index: usize,
}

impl<'a> Iterator for LookupHtblIter<'a> {
    type Item = (&'a [u8], &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.table_index >= self.htbl.table.len() {
                return None;
            }
            let data_index = read_index(&self.htbl.table, self.table_index + 1);
            self.table_index += ENTRY_SIZE;
            if data_index != 0usize {
                let key_len = read_index(&self.htbl.data, data_index);
                let key_index = data_index + INDEX_SIZE;
                let value_len_index = key_index + key_len;
                let value_len = read_index(&self.htbl.data, value_len_index);
                let value_index = value_len_index + INDEX_SIZE;
                return Some((&self.htbl.data[key_index..key_index + key_len], &self.htbl.data[value_index..value_index + value_len]));
            }
        }
    }
}

impl<'a> IntoIterator for &'a LookupHtbl {
    type Item = (&'a [u8], &'a [u8]);
    type IntoIter = LookupHtblIter<'a>;

    // Required method
    fn into_iter(self) -> Self::IntoIter {
        LookupHtblIter {
            htbl: &self,
            table_index: 0usize,
        }
    }
}

// Reduce maps a random value in the range [0..2^32] to [0..N], which is used to compute the index
// into the hash table.  This is faster than computing x % M.
fn reduce(x: u32, n: u32) -> usize {
    (((x as u64) * (n as u64)) >> 32) as usize
}

// Read a u40 index from unaligned memory LE, and return it as a usize.
#[inline]
fn read_index(data: &[u8], index: usize) -> usize {
    let mut val = [0u8; 8];
    (&mut val[0..INDEX_SIZE]).copy_from_slice(&data[index..index + INDEX_SIZE]);
    u64::from_le_bytes(val) as usize
}

// Write a u40 index to unaligned memory LE.
#[inline]
fn write_index(data: &mut [u8], index: usize, value: usize) {
    let data = &mut data[index..index + INDEX_SIZE];
    data.copy_from_slice(&value.to_le_bytes()[0..INDEX_SIZE]);
}

// Multiplication is our best fast mixing primitive, and with XOR, we have a non-linear hash.  We
// multiply by odd numbers so it is reversible.  The upper 32 bits of the result of a 64x64->64
// multiplication has a good mix from the lower 32 bits, but the upper 32 bits of the input do not
// effect the result's lower 32 bits.  Therefore, multiply by v + (v >> 32), so that high and low
// bits influence the high bits of the result.  Then, mix the upper 32 bits into the lower 32.
#[inline]
fn hash_u64(v: u64) -> u64 {
    let v1 =
        u64::wrapping_mul(u64::wrapping_add(v, v >> 32), 0xcafebabedeadbeefu64) ^ 0x013456789abcdef;
    u64::wrapping_add(v1, v1 >> 32)
}

#[inline]
fn hash(v: &[u8]) -> u64 {
    let mut i = 0usize;
    let mut val = 0u64;
    let mut bytes = [0u8; 8];
    while i + 8 <= v.len() {
        bytes.copy_from_slice(&v[i..i + 8]);
        let digit = u64::from_le_bytes(bytes);
        val = hash_u64(val ^ digit);
        i += 8;
    }
    if i < v.len() {
        bytes[0..v.len() - i].copy_from_slice(&v[i..v.len()]);
        let digit: u64 = u64::from_le_bytes(bytes);
        val = hash_u64(val ^ digit);
    }
    val
}

#[cfg(test)]
mod tests {
    use super::*;

    const NUM_KEYS: usize = 1_000_000usize;
    const NUM_LOOKUPS: usize = 1_000_000usize;
    const AVE_VALUE_SIZE: usize = 60usize;

    #[test]
    fn test_lookup_htbl() {
        let mut table = LookupHtbl::new();
        table.try_reserve(NUM_KEYS as u64, (NUM_KEYS * (8 + AVE_VALUE_SIZE)) as u64).unwrap();
        let mask: u64 = (NUM_KEYS.next_power_of_two() - 1) as u64;
        let mut num_keys = 0usize;
        let mut key_bytes = [0u8; 8];
        while num_keys < NUM_KEYS {
            let key = num_keys as u64;
            key_bytes.copy_from_slice(&key.to_le_bytes());
            if !table.contains_key(&key_bytes) {
                let mut value = [key_bytes[1]; AVE_VALUE_SIZE];
                value[0] = key_bytes[0] as u8;
                value[AVE_VALUE_SIZE - 1] = key_bytes[7];
                table.insert(&key_bytes, &value);
                num_keys += 1;
            }
        }
        assert!(table.used_data == NUM_KEYS * (2 * INDEX_SIZE + 8 + AVE_VALUE_SIZE) + 1);
        let mut hits = 0;
        let mut misses = 0;
        let mut total = 0u64;
        for i in 0u64..NUM_LOOKUPS as u64 {
            let key = hash_u64(i) & mask;
            match table.get(&key.to_le_bytes()) {
                Some(val) => {
                    hits += 1;
                    total += val[5] as u64;
                    assert!(val[0] == (key as u8));
                }
                None => misses += 1,
            }
        }
        assert!(hits != 0 && misses != 0 && total != 0);
    }

    #[test]
    fn test_for_loop() {
        let keys = ["key1".as_bytes(), "key2".as_bytes(), "key3".as_bytes()];
        let values = ["value1".as_bytes(), "value2".as_bytes(), "value3".as_bytes()];
        let mut table = LookupHtbl::new();
        table.try_reserve(3u64, 3u64 * 10u64).unwrap();
        for i in 0..3 {
            table.insert(keys[i], values[i]);
        }
        let mut found = [false, false, false];
        for (key, value) in &table {
            if key == keys[0] {
                found[0] = true;
                assert!(value == values[0]);
            } else if key == keys[1] {
                found[1] = true;
                assert!(value == values[1]);
            } else if key == keys[2] {
                found[2] = true;
                assert!(value == values[2]);
            }
        }
        assert!(found[0] && found[1] && found[2]);
    }
}
