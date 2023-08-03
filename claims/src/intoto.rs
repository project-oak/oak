//
// Copyright 2023 The Project Oak Authors
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

//! This module contains structs for specifying in-toto statements.

extern crate alloc;

use alloc::{collections::BTreeMap, string::String, vec::Vec};
use serde::{Deserialize, Serialize};

/// URI representing in-toto v01 statements. This is constant for all predicate
/// types.
pub const STATEMENT_INTOTO_V01: &str = "https://in-toto.io/Statement/v0.1";

/// Trait representing a predicate about a software artifact.
pub trait Predicate {}

// A map from algorithm name to lowercase hex-encoded value.
pub type DigestSet = BTreeMap<String, String>;

/// A software artifact identified by its name and a set of artifacts.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Subject {
    pub name: String,
    pub digest: DigestSet,
}

/// This struct represents a generic statement that binds a predicate to a
/// particular subject.
#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct Statement<P: Predicate> {
    pub _type: String,
    #[serde(rename = "predicateType")]
    pub predicate_type: String,
    pub subject: Vec<Subject>,
    pub predicate: P,
}
