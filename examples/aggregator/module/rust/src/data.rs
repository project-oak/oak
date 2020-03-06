//
// Copyright 2020 The Project Oak Authors
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

use crate::proto::aggregator::SerializedSparseVector;
use aggregator_common::Monoid;
use std::collections::HashMap;
use std::convert::{From, TryFrom};

// Sparce Vectors are stored as Hash Maps.
#[derive(Debug)]
pub struct SparseVector {
    map: HashMap<u32, f32>,
}

// Deserializes a Protobuf message into an internal Sparce Vector implementation.
// If a Protobuf message has duplicated indices, returns an `Error`.
impl TryFrom<SerializedSparseVector> for SparseVector {
    type Error = &'static str;

    fn try_from(src: SerializedSparseVector) -> Result<Self, Self::Error> {
        src.indices.iter().zip(src.values.iter()).try_fold(
            SparseVector::identity(),
            |mut svec, (&i, &v)| match svec.map.get(&i) {
                Some(_) => Err("Duplicated index"),
                None => Ok({
                    svec.map.insert(i, v);
                    svec
                }),
            },
        )
    }
}

// Serializes an internal Sparce Vector implementation into a Protobuf message.
impl From<SparseVector> for SerializedSparseVector {
    fn from(src: SparseVector) -> Self {
        src.map
            .iter()
            .fold(SerializedSparseVector::new(), |mut vec, (&i, &v)| {
                vec.indices.push(i);
                vec.values.push(v);
                vec
            })
    }
}

impl Monoid for SparseVector {
    fn identity() -> Self {
        SparseVector {
            map: HashMap::new(),
        }
    }

    /// ...
    fn combine(&self, other: &Self) -> Self {
        // other.map.iter().fold(*self.clone(), |mut svec, (&i, &v)| {
        //     *svec.map.entry(i).or_insert(v) += v;
        //     svec
        // })
        other.map
            .iter()
            .for_each(|(&i, &v)| {
                self.map.entry(i).or_insert(v) += v;
            })
    }
}
