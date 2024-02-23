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

//! This is a key/value hash table optimized for large numbers of small k/v pairs.  We assume we
//! bust out of on-chip cache, so speed is limited by cache misses, not the actual operations such
//! as hashing and bit manipulation.
//!
//! The k/v pairs are loaded before any are read, and once they are loaded cannot be modified.  We
//! take advantage of these restrictions to build a hash table with far less memory overhead per
//! k/v pair (21 bytes vs ~128 bytes for hashbrown<Bytes, Bytes>).  Speed for k/v lookups is ~90ns
//! on manual tests.
//!
//! The hash table consists of 2 vectors.  The first is a table of "entries", which is a packed
//! array of entries with the following layout:
//!
//! ```ignore
//!    hash_byte: u8,
//!    data_index: u40,  // A 5-byte index, so we support up to 1TiB of data.
//! ```
//!
//! This is a "swiss" table meaning that instead of the usual "buckets" of entries, the entries are
//! collapsed into the hash table itself.  By adding a 1-byte hash, we can eliminate 99.6% of key
//! comparisons to the wrong keys.  This is important for speed because comparing keys causes a
//! page fault usually, while comparing the 1-byte hash is usually an L1 cache hit.  The number of
//! cache misses per lookup should be close to 2 for values found in the table, and 1 for values
//! not in the table.
//!
//! The storage for k/v pairs is chunked into 2MiB vectors:
//!
//! ```ignore
//!     data_chunks: Vec<Box<[u8]>>,
//! ```
//!
//! `data_chunks` starts empty, and as data is added to the table, we allocate another chunk.  The
//! format for each k/v pair of data in each chunk is:
//!
//! ```ignore
//!     key_len: <compressed u30>
//!     key: [u8]
//!     value_len: <compressed u30>
//!     value: [u8]
//! ```
//!
//! Another memory savings comes from using a swiss table with exactly a 60% load factor.  Swiss
//! tables require a significant portion of the table be empty, and normally as the table grows,
//! they dynamically double the size.  At least when using the alloc crate, this resize causes a
//! new table to be allocated at 2X the size, data is copied from the old table to the new, and the
//! old table is freed.  This results in a 3X expansion in memory usage vs the prior array size.
//! In contrast, this scheme has only 40% of the table empty and is never resized.
//!
//! There are certain limits imposed by this structure:
//!
//!   * Every k/v pair must fit into a 2MiB chunk.
//!   * The total memory allocated to keys and values, and their compressed lengths, is < 1TiB.

use alloc::{boxed::Box, vec, vec::Vec};
use core::mem;

use bytes::Bytes;

// To save memory, we use 5 byte array index values instead of 8 bytes.  This saves 12 bytes per
// k/v pair.  It is referred to as u40 below.
const INDEX_SIZE: usize = 5;

const CHUNK_BITS: usize = 21;
const CHUNK_SIZE: usize = 1 << CHUNK_BITS;
const CHUNK_MASK: usize = CHUNK_SIZE - 1;

#[derive(Clone, Copy, Default)]
struct Entry {
    hash_byte: u8,
    data_index: [u8; 5],
}

#[derive(Default)]
pub struct LookupHtbl {
    table: Vec<Entry>, // Contains fixed-size entries with index of k/v data in data_chunks.
    data_chunks: Vec<Box<[u8]>>,
    max_entries: usize,       // The number at which we must grow the table.
    used_data: usize,
    used_entries: usize,
}

// Retured by LookupHtbl::lookup.
enum LookupResult {
    Found(usize, usize), // (table_index: u40, data_index: u40)
    NotFound(usize, u8), // (table_index: u40, hash_byte: u8)
}

impl LookupHtbl {
    /// Set the initial size of self.table.  For best speed and memory use, this should be as large
    /// as the number of key/value entries that will be loaded.
    pub fn reserve(&mut self, max_entries: usize) {
        assert!(self.used_entries == 0 && self.used_data == 0);
        // Use a load factor of 60%.
        let allocated_entries = (5 * max_entries + 1) / 3;
        self.max_entries = max_entries;
        self.table = vec![Entry::default(); allocated_entries];
        // Allocate 1 extra byte, so the 0 index can be used as NULL.
        self.data_chunks = vec![];
        self.used_data = 1usize;
        self.used_entries = 0usize;
    }

    // Lookup the key/value pair.  If found, return LookupResult::Found(table_index, data_index).
    // Otherwise, return the LookupResult::NotFound(table index, hash_byte).
    fn lookup(&self, key: &[u8]) -> LookupResult {
        if self.table.is_empty() {
            panic!("Check for emtpy before calling lookup");
        }
        let key_hash: u64 = hash(key);
        let key_hash_byte = key_hash as u8;
        let mut table_index = reduce(key_hash as u32, self.table.len() as u32);
        let mut data_index: usize;
        loop {
            // We try to load only the hash byte to save time.  Once we have a matching hash byte,
            // the loop ends and we compare keys.
            let mut entry = &self.table[table_index];
            while entry.hash_byte != key_hash_byte {
                if entry.hash_byte == 0 {
                    data_index = read_index(&entry.data_index);
                    if data_index == 0usize {
                        return LookupResult::NotFound(table_index, key_hash_byte);
                    }
                }
                table_index += 1;
                if table_index == self.table.len() {
                    table_index = 0;
                }
                entry = &self.table[table_index];
            }
            data_index = read_index(&entry.data_index);
            if data_index == 0usize {
                // This only happens if the key hash byte is 0.
                return LookupResult::NotFound(table_index, key_hash_byte);
            }
            let chunk: &[u8] = &self.data_chunks[data_index >> CHUNK_BITS];
            let index = data_index & CHUNK_MASK;
            let (key_len, key_len_size) = read_len(chunk, index);
            let key_index = index + key_len_size;
            let entry_key: &[u8] = &chunk[key_index..key_index + key_len];
            if entry_key == key {
                return LookupResult::Found(table_index, data_index);
            }
            table_index += 1;
            if table_index == self.table.len() {
                table_index = 0;
            }
        }
    }

    /// This is like HashMapp::contains_key.
    pub fn contains_key(&self, key: &[u8]) -> bool {
        if self.table.is_empty() {
            return false;
        }
        matches!(self.lookup(key), LookupResult::Found(_, _))
    }

    /// This is like HashMapp::get.
    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        if self.is_empty() {
            return None;
        }
        match self.lookup(key) {
            LookupResult::Found(_, data_index) => Some(self.get_value(data_index)),
            LookupResult::NotFound(_, _) => None,
        }
    }

    // Return the value associated with the k/v pair at data_index.
    fn get_value(&self, data_index: usize) -> &[u8] {
        let chunk: &[u8] = &self.data_chunks[data_index >> CHUNK_BITS];
        let index = data_index & CHUNK_MASK;
        let (key_len, key_len_size) = read_len(chunk, index);
        let value_len_index = index + key_len_size + key_len;
        let (value_len, value_len_size) = read_len(chunk, value_len_index);
        let value_index = value_len_index + value_len_size;
        &chunk[value_index..value_index + value_len]
    }

    /// Insert a k/v pair into the table.  Returns None if the key was not already in the table,
    /// and Some(&[u8]) referring to the prior value otherwise.
    pub fn insert(&mut self, key: &[u8], value: &[u8]) -> Option<&[u8]> {
        if self.table.is_empty() {
            self.reserve(1);
        } else if self.used_entries >= self.max_entries {
            // This should never happen if the needed space is reserved first.
            self.grow_table();
        }
        let data_index = self.new_data(key, value);
        match self.lookup(key) {
            LookupResult::Found(table_index, old_data_index) => {
                let entry = &mut self.table[table_index];
                write_index(&mut entry.data_index, data_index);
                Some(self.get_value(old_data_index))
            }
            LookupResult::NotFound(table_index, hash_byte) => {
                let entry = &mut self.table[table_index];
                entry.hash_byte = hash_byte;
                write_index(&mut entry.data_index, data_index);
                self.used_entries += 1;
                None
            }
        }
    }

    // This increases memory for the table temporarily increase 3X, and permanently by 2X.
    fn grow_table(&mut self) {
        if self.max_entries == 0 {
            self.reserve(1);
            return;
        }
        let old_table = mem::take(&mut self.table);
        self.table = vec![Entry::default(); old_table.len() << 1];
        self.max_entries <<= 1;
        for i in 0..old_table.len() {
            let raw_index = read_index(&old_table[i].data_index);
            if raw_index != 0 {
                let chunk: &[u8] = &self.data_chunks[raw_index >> CHUNK_BITS];
                let index = raw_index & CHUNK_MASK;
                let (key_len, key_len_size) = read_len(chunk, index);
                let key_index = index + key_len_size;
                let key: &[u8] = &chunk[key_index..key_index + key_len];
                match self.lookup(key) {
                    LookupResult::NotFound(table_index, hash_byte) => {
                        let entry = &mut self.table[table_index];
                        entry.hash_byte = hash_byte;
                        write_index(&mut entry.data_index, raw_index);
                    }
                    _ => panic!("New table should not already have this key"),
                }
            }
        }
    }

    // Create a k/v pair in the most recent chunk.  Create a new chunk if this would overflow.
    fn new_data(&mut self, key: &[u8], value: &[u8]) -> usize {
        // Check to see if we need a new chunk.  INDEX_SIZE is also the max for compressed ints.
        let additional_data_len = 2 * INDEX_SIZE + key.len() + value.len();
        assert!(additional_data_len < CHUNK_SIZE);
        let end_index = self.used_data + additional_data_len;
        let chunk_index = end_index >> CHUNK_BITS;
        if self.data_chunks.len() <= chunk_index {
            let values = Box::<[u8]>::new_zeroed_slice(CHUNK_SIZE);
            let values = unsafe { values.assume_init() };
            self.data_chunks.push(values);
            if chunk_index == 0 {
                self.used_data = 1; // Address 0 is NULL.
            } else {
                self.used_data = CHUNK_SIZE * chunk_index;
            }
        }
        let chunk: &mut [u8] = &mut self.data_chunks[chunk_index];
        let index = self.used_data & CHUNK_MASK;
        let key_index = index + write_len(chunk, index, key.len());
        chunk[key_index..key_index + key.len()].copy_from_slice(key);
        let value_len_index = key_index + key.len();
        let value_index = value_len_index + write_len(chunk, value_len_index, value.len());
        chunk[value_index..value_index + value.len()].copy_from_slice(value);
        let used_data = self.used_data;
        self.used_data += value_index + value.len() - index;
        used_data
    }

    /// This is like HashMap::extend.
    pub fn extend<T: IntoIterator<Item = (Bytes, Bytes)>>(&mut self, new_data: T) {
        for (key, value) in new_data {
            self.insert(&key, &value);
        }
    }

    /// Return the number of entries in the hash table.
    pub fn len(&self) -> usize {
        self.used_entries
    }

    /// Return true if there are no entries in the hash table.
    pub fn is_empty(&self) -> bool {
        self.used_entries == 0
    }

    /// Return an iterator that can be used to iterate through k/v pairs.
    pub fn iter(&self) -> LookupHtblIter {
        LookupHtblIter {
            htbl: self,
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
            let raw_index = read_index(&self.htbl.table[self.table_index].data_index);
            self.table_index += 1;
            if raw_index != 0usize {
                let chunk: &[u8] = &self.htbl.data_chunks[raw_index >> CHUNK_BITS];
                let index = raw_index & CHUNK_MASK;
                let (key_len, key_len_size) = read_len(chunk, index);
                let key_index = index + key_len_size;
                let value_len_index = key_index + key_len;
                let (value_len, value_len_size) = read_len(chunk, value_len_index);
                let value_index = value_len_index + value_len_size;
                return Some((
                    &chunk[key_index..key_index + key_len],
                    &chunk[value_index..value_index + value_len],
                ));
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
            htbl: self,
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
fn read_index(data: &[u8; 5]) -> usize {
    let mut val = [0u8; 8];
    val[0..INDEX_SIZE].copy_from_slice(data);
    u64::from_le_bytes(val) as usize
}

// Write a u40 index to unaligned memory LE.
#[inline]
fn write_index(data: &mut [u8; 5], value: usize) {
    data.copy_from_slice(&value.to_le_bytes()[0..INDEX_SIZE]);
}

// Read a compressed integer length.  Returns (length, num bytes of length) Compressed integers for
// lengths are <2-bit num_bytes><6-bit MSBs>.  num_bytes is 0 for small integers <= 64.  Lengths up
// to 2^30 can be represented, limiting keys and values to 1GiB each.
#[inline]
fn read_len(data: &[u8], index: usize) -> (usize, usize) {
    let first_byte = data[index] as usize;
    if first_byte < 64 {
        return (first_byte, 1usize);
    }
    let num_bytes = first_byte >> 6;
    let mut val = [0u8; 8];
    val[0..num_bytes].copy_from_slice(&data[index + 1..index + 1 + num_bytes]);
    let len = u64::from_le_bytes(val) as usize;
    let len = len | ((first_byte & 0x3f) << (8 * num_bytes));
    (len, 1 + num_bytes)
}

// Write a compressed length to data.  Return the number of bytes used to represent the length.
#[inline]
fn write_len(data: &mut [u8], index: usize, len: usize) -> usize {
    if len < 64 {
        data[index] = len as u8;
        return 1usize;
    }
    let mut l = len;
    let mut num_bytes = 1usize;
    while l >= 64 {
        data[index + num_bytes] = l as u8;
        l >>= 8;
        num_bytes += 1;
    }
    let first_byte = ((num_bytes - 1) << 6 | l) as u8;
    data[index] = first_byte;
    num_bytes
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
    const AVE_VALUE_SIZE: usize = 60;

    #[test]
    fn test_lookup_htbl() {
        let mut table = LookupHtbl::default();
        table.reserve(NUM_KEYS);
        let mask: u64 = (NUM_KEYS.next_power_of_two() - 1) as u64;
        let mut num_keys = 0usize;
        let mut key_bytes = [0u8; 8];
        while num_keys < NUM_KEYS {
            let key = num_keys as u64;
            key_bytes.copy_from_slice(&key.to_le_bytes());
            if !table.contains_key(&key_bytes) {
                let mut value = [key_bytes[1]; AVE_VALUE_SIZE];
                value[0] = key_bytes[0];
                value[AVE_VALUE_SIZE - 1] = key_bytes[7];
                table.insert(&key_bytes, &value);
                num_keys += 1;
            } else {
                panic!("Should not already have this key");
            }
        }
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
        let values = [
            "value1".as_bytes(),
            "value2".as_bytes(),
            "value3".as_bytes(),
        ];
        let mut table = LookupHtbl::default();
        table.reserve(3);
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

    // This further tests the hash function.
    struct Rand {
        seed: u64,
    }

    impl Rand {
        fn rand64(&mut self) -> u64 {
            self.seed = hash_u64(self.seed);
            self.seed
        }

        fn rand_range(&mut self, n: usize) -> usize {
            self.rand64() as usize % n
        }

        fn rand_bytes(&mut self, len: usize) -> Vec<u8> {
            let mut v = vec![];
            for _ in 0..len {
                v.push(self.seed as u8);
                self.seed = hash_u64(self.seed);
            }
            v
        }

        fn rand_kv_pair(&mut self, key_len: usize, value_len: usize) -> (Vec<u8>, Vec<u8>) {
            let key_len = self.rand_range(key_len);
            let value_len = self.rand_range(value_len);
            let key = self.rand_bytes(key_len);
            let value = self.rand_bytes(value_len);
            (key, value)
        }
    }

    #[test]
    fn test_rand_vals() {
        let mut r = Rand { seed: 0u64 };
        let mut kv_pairs: Vec<(Vec<u8>, Vec<u8>)> = vec![];
        let mut table = LookupHtbl::default();
        for _ in 0..2 {
            loop {
                let kv_pair = r.rand_kv_pair(100, 1000);
                if !table.contains_key(&kv_pair.0) {
                    table.insert(&kv_pair.0, &kv_pair.1);
                    kv_pairs.push(kv_pair);
                    break;
                }
            }
        }
        for kv_pair in kv_pairs {
            assert!(table.get(&kv_pair.0) == Some(&kv_pair.1));
        }
    }

    // The hash function should act like a random oracle, in which case the odds of seeing the same
    // value as one that came before is determined by the Birthday Problem.  Using the rule of
    // thumb for how large the sequence needs to be to have a .5 probability of collision: sqrt(0.5
    // * ln(2) * 2^64) = 2.5e9.  This test just checks that one seed leads to a sequence longer
    // than 2^30 without collisions.
    #[test]
    fn test_rng_sequence_len() {
        // If the sequence length < 2^30, we can find it by stepping 2^30, and then stepping
        // another 2^30 looking for the value we saw at 2^30.
        let mut r = Rand { seed: 0u64 };
        for _ in 0usize..1usize << 30 {
            r.rand64();
        }
        let target = r.rand64();
        for _ in 0usize..1usize << 26 {
            if r.rand64() == target {
                panic!("RNG sequence too short");
            }
        }
    }

    #[test]
    fn test_dumplicate_key() {
        let mut table = LookupHtbl::default();
        table.insert("key".as_bytes(), "value1".as_bytes());
        assert!(table.get("key".as_bytes()) == Some("value1".as_bytes()));
        table.insert("key".as_bytes(), "value2".as_bytes());
        assert!(table.get("key".as_bytes()) == Some("value2".as_bytes()));
    }
}
