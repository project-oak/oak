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

use super::*;

/// A [`Runnable`] command that checks for the existence of todos in the codebase with no associated
/// GitHub issue number.
pub struct CheckTodo {
    path: String,
}

impl CheckTodo {
    pub fn new(path: String) -> Box<Self> {
        Box::new(CheckTodo { path })
    }
}

impl Runnable for CheckTodo {
    fn description(&self) -> String {
        "check todo".to_string()
    }

    fn run(self: Box<Self>, _opt: &Opt) -> Box<dyn Running> {
        let file_content = std::fs::read_to_string(&self.path).expect("could not read file");
        let todo_words = file_content
            .split_whitespace()
            // We cannot use the TO DO word all together here, because otherwise it would trigger
            // the very logic that this struct is implementing.
            // TODO(#396): Use a regex to match on a more precise format.
            .filter(|word| word.contains(&format!("{}{}", "TO", "DO")))
            .filter(|word| {
                !(word.starts_with(&format!("{}{}(", "TO", "DO"))
                    && (word.ends_with("):") || word.ends_with(')')))
            })
            .collect::<Vec<_>>();
        let result = if todo_words.is_empty() {
            SingleStatusResult {
                value: StatusResultValue::Ok,
                logs: String::new(),
            }
        } else {
            SingleStatusResult {
                value: StatusResultValue::Error,
                logs: format!("Invalid todos: {:?}", todo_words),
            }
        };
        Box::new(result)
    }
}
