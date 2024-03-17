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

use std::path::Path;

use crate::{files::file_contains, internal::*};

/// A [`Runnable`] command that checks for the existence of source files without
/// the necessary license header.
pub struct CheckLicense {
    path: String,
}

impl CheckLicense {
    pub fn new(path: String) -> Box<Self> {
        Box::new(CheckLicense { path })
    }
}

impl Runnable for CheckLicense {
    fn description(&self) -> String {
        "check license".to_string()
    }

    fn run(self: Box<Self>, _opt: &Opt) -> Box<dyn Running> {
        let result_value = if file_contains(Path::new(&self.path), "Apache License") {
            StatusResultValue::Ok
        } else {
            StatusResultValue::Error
        };
        Box::new(SingleStatusResult { value: result_value, logs: String::new() })
    }
}
