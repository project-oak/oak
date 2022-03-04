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
use once_cell::sync::Lazy;
use regex::Regex;

static PATTERN: Lazy<Regex> =
    // Break up "TO" and "DO" to avoid false positives on this code.
    Lazy::new(|| Regex::new(&format!(r"{}DO\(#\d+\)", "TO")).expect("Could not parse regex"));

/// A [`Runnable`] command that checks for the existence of todos in the codebase with no associated
/// GitHub issue number.
pub struct CheckTodo {
    path: String,
}

impl CheckTodo {
    pub fn new(path: String) -> Box<Self> {
        Box::new(CheckTodo { path })
    }

    fn is_invalid_todo(word: &str) -> bool {
        // Break up "TO" and "DO" to avoid false positives on this code.
        word.contains(&format!("{}DO", "TO")) && !PATTERN.is_match(word)
    }
}

impl Runnable for CheckTodo {
    fn description(&self) -> String {
        "check todo".to_string()
    }

    fn run(self: Box<Self>, _opt: &Opt) -> Box<dyn Running> {
        let file_content = std::fs::read_to_string(&self.path).expect("could not read file");
        let invalid_todo_words = file_content
            .split_whitespace()
            .filter(|word| CheckTodo::is_invalid_todo(word))
            .collect::<Vec<_>>();
        let result = if invalid_todo_words.is_empty() {
            SingleStatusResult {
                value: StatusResultValue::Ok,
                logs: String::new(),
            }
        } else {
            SingleStatusResult {
                value: StatusResultValue::Error,
                logs: format!("Invalid todos: {:?}", invalid_todo_words),
            }
        };
        Box::new(result)
    }
}

#[cfg(test)]
mod tests {
    use super::CheckTodo;
    #[test]
    fn check_todos() {
        assert!(CheckTodo::is_invalid_todo(&format!("{}DO()", "TO")));
        assert!(!CheckTodo::is_invalid_todo(&format!("{}DO(#123)", "TO")));
    }
}
