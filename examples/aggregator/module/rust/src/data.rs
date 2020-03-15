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

// Sparse Vectors are stored as Hash Maps.
#[derive(Clone, Debug)]
pub struct SparseVector {
    entries: HashMap<u32, f32>,
}

// Deserializes a Protobuf message into an internal Sparce Vector implementation.
// If a Protobuf message has duplicated indices, returns an `Error`.
impl TryFrom<SerializedSparseVector> for SparseVector {
    type Error = String;

    fn try_from(src: SerializedSparseVector) -> Result<Self, Self::Error> {
        src.indices.iter().zip(src.values.iter()).try_fold(
            SparseVector::identity(),
            |mut svec, (&i, &v)| match svec.entries.get(&i) {
                Some(_) => Err(format!("Duplicated index: {}", i)),
                None => Ok({
                    svec.entries.insert(i, v);
                    svec
                }),
            },
        )
    }
}

// Serializes an internal Sparce Vector implementation into a Protobuf message.
impl From<SparseVector> for SerializedSparseVector {
    fn from(src: SparseVector) -> Self {
        src.entries
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
            entries: HashMap::new(),
        }
    }

    /// Combines two Sparse Vectors by adding up values corresponding to the same keys.
    fn combine(&self, other: &Self) -> Self {
        other.entries.iter().fold(self.clone(), |mut svec, (&i, &v)| {
            *svec.entries.entry(i).or_insert(v) += v;
            svec
        })
    }
}
