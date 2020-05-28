// Copyright 2017-2019 int08h LLC
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

//!
//! Adds deliberate errors to client responses as part of the
//! [Roughtime Ecosystem](https://roughtime.googlesource.com/roughtime/+/HEAD/ECOSYSTEM.md#maintaining-a-healthy-software-ecosystem).
//!
//! See the documentation for [ServerConfig](../config/trait.ServerConfig.html#tymethod.fault_percentage)
//! on how to enable.
//!

use rand::{FromEntropy, Rng};
use rand::distributions::Bernoulli;
use rand::rngs::SmallRng;
use rand::seq::SliceRandom;
use rand::seq::index::sample as index_sample;

use crate::RtMessage;
use crate::tag::Tag;
use crate::grease::Pathologies::*;
use crate::SIGNATURE_LENGTH;

///
/// Ways that a message can be made invalid.
///
pub enum Pathologies {
    /// Randomly re-order the (tag, value) pairs in the message. This violates the protocol's
    /// requirement that tags must be in strictly increasing order.
    RandomlyOrderTags,

    /// Replace the server's signature (value of the SIG tag) with random garbage.
    CorruptResponseSignature,

    // TODO(stuart) semantic pathologies
}

static ALL_PATHOLOGIES: &[Pathologies] = &[
    RandomlyOrderTags,
    CorruptResponseSignature
];

///
/// Adds deliberate errors to client responses as part of the
/// [Roughtime Ecosystem](https://roughtime.googlesource.com/roughtime/+/HEAD/ECOSYSTEM.md#maintaining-a-healthy-software-ecosystem).
///
pub struct Grease {
    enabled: bool,
    dist: Bernoulli,
    prng: SmallRng,
}

impl Grease {
    ///
    /// Creates a new instance `fault_percentage` likely to corrupt a source message.
    ///
    pub fn new(fault_percentage: u8) -> Self {
        Grease {
            enabled: fault_percentage > 0,
            dist: Bernoulli::from_ratio(u32::from(fault_percentage), 100),
            prng: SmallRng::from_entropy(),
        }
    }

    ///
    /// Returns true `fault_percentage` percent of the time.
    ///
    #[inline]
    pub fn should_add_error(&mut self) -> bool {
        if self.enabled { self.prng.sample(self.dist) } else { false }
    }

    ///
    /// Returns a *new* `RtMessage` that has been altered to be deliberately invalid.
    ///
    /// The type of alteration made to `src_msg` is randomly chosen from from
    /// [Pathologies](enum.Pathologies.html)
    ///
    pub fn add_errors(&mut self, src_msg: &RtMessage) -> RtMessage {
        match ALL_PATHOLOGIES.choose(&mut self.prng) {
            Some(CorruptResponseSignature) => self.corrupt_response_signature(src_msg),
            Some(RandomlyOrderTags) => self.randomly_order_tags(src_msg),
            None => unreachable!()
        }
    }

    ///
    /// Randomly shuffle ordering of the (tag, value) pairs in the source message.
    ///
    fn randomly_order_tags(&mut self, src_msg: &RtMessage) -> RtMessage {
        let src_tags = src_msg.tags();
        let src_values = src_msg.values();
        let num_fields = src_msg.num_fields() as usize;

        let mut new_tags: Vec<Tag> = Vec::with_capacity(num_fields);
        let mut new_values: Vec<Vec<u8>> = Vec::with_capacity(num_fields);

        // TODO(stuart) use replacement instead of copying
        for idx in index_sample(&mut self.prng, num_fields, num_fields).iter() {
            new_tags.push(*src_tags.get(idx).unwrap());
            new_values.push(src_values.get(idx).unwrap().to_vec());
        }

        RtMessage::new_deliberately_invalid(new_tags, new_values)
    }

    ///
    /// Replace valid SIG signature with random garbage
    ///
    fn corrupt_response_signature(&self, src_msg: &RtMessage) -> RtMessage {
        if src_msg.get_field(Tag::SIG).is_none() {
            return src_msg.to_owned();
        }

        let mut prng = SmallRng::from_entropy();
        let mut random_sig: [u8; SIGNATURE_LENGTH as usize] = [0u8; SIGNATURE_LENGTH as usize];

        prng.fill(&mut random_sig);

        let mut new_msg = RtMessage::new(src_msg.num_fields());
        new_msg.add_field(Tag::SIG, &random_sig).unwrap();
        new_msg.add_field(Tag::PATH, src_msg.get_field(Tag::PATH).unwrap()).unwrap();
        new_msg.add_field(Tag::SREP, src_msg.get_field(Tag::SREP).unwrap()).unwrap();
        new_msg.add_field(Tag::CERT, src_msg.get_field(Tag::CERT).unwrap()).unwrap();
        new_msg.add_field(Tag::INDX, src_msg.get_field(Tag::INDX).unwrap()).unwrap();

        new_msg
    }
}

#[cfg(test)]
mod test {
    use crate::grease::Grease;
    use crate::RtMessage;
    use crate::tag::Tag;

    #[test]
    fn verify_error_probability() {
        const TRIALS: u64 = 100_000;
        const TOLERANCE: f64 = 0.75;

        for target in 1..50 {
            let mut g = Grease::new(target);
            let (lower, upper) = (target as f64 - TOLERANCE, target as f64 + TOLERANCE);

            let acc: u64 = (0..TRIALS)
                .map(|_| if g.should_add_error() { 1 } else { 0 })
                .sum();

            let percentage = 100.0 * (acc as f64 / TRIALS as f64);

            assert_eq!(
                percentage > lower && percentage < upper,
                true,
                "target {}, actual {} [{}, {}]", target, percentage, lower, upper
            );
        }
    }

    #[test]
    fn check_tag_reordering() {
        let pairs = [
            (Tag::SIG, [b'0']),
            (Tag::NONC, [b'1']),
            (Tag::DELE, [b'2']),
            (Tag::PATH, [b'3']),
            (Tag::RADI, [b'4']),
            (Tag::PUBK, [b'5']),
            (Tag::MIDP, [b'6']),
            (Tag::SREP, [b'7']),
            (Tag::MINT, [b'8']),
            (Tag::ROOT, [b'9']),
            (Tag::CERT, [b'a']),
            (Tag::MAXT, [b'b']),
            (Tag::INDX, [b'c']),
            (Tag::PAD, [b'd'])
        ];

        let mut msg = RtMessage::new(14);
        for pair in &pairs {
            msg.add_field(pair.0, &pair.1).unwrap();
        }

        let mut grease = Grease::new(1);
        let reordered = grease.randomly_order_tags(&msg);
        println!("orig: {:?}\nnew:  {:?}", msg.tags(), reordered.tags());

        // original and reordered are same length
        assert_eq!(msg.num_fields(), reordered.num_fields());

        // the shuffle took place
        assert_ne!(msg.tags(), reordered.tags());
        assert_ne!(msg.values(), reordered.values());

        // tag still points to same value
        for (tag, _) in pairs.iter() {
            assert_eq!(msg.get_field(*tag).unwrap(), reordered.get_field(*tag).unwrap());
        }
    }

    #[test]
    fn check_signature_corruption() {
        let mut msg = RtMessage::new(5);
        msg.add_field(Tag::SIG, &[b'a']).unwrap();
        msg.add_field(Tag::PATH, &[b'0']).unwrap();
        msg.add_field(Tag::SREP, &[b'1']).unwrap();
        msg.add_field(Tag::CERT, &[b'2']).unwrap();
        msg.add_field(Tag::INDX, &[b'3']).unwrap();

        let grease = Grease::new(1);
        let changed = grease.corrupt_response_signature(&msg);

        println!("orig: {:?}\nnew:  {:?}", msg.get_field(Tag::SIG), changed.get_field(Tag::SIG));

        assert_ne!(msg.get_field(Tag::SIG).unwrap(), changed.get_field(Tag::SIG).unwrap());
    }
}
