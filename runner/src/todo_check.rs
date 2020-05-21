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

use crate::internal::{status_combine, SingleStatusResult, StatusResultValue};
use regex::Regex;
use std::{
    io::{BufRead, BufReader},
    path::PathBuf,
};

pub struct TodoChecker {
    // Path to check for to-do marker problems.
    path: PathBuf,
    todo_re: regex::Regex,
    details_re: regex::Regex,
}

impl TodoChecker {
    pub fn new(path: &PathBuf) -> Self {
        TodoChecker {
            path: path.clone(),
            // Break up "TO" and "DO" to avoid false positives on this code.
            todo_re: Regex::new(&format!(r"{}DO(?P<details>[^:]+)?:", "TO")).unwrap(),
            details_re: Regex::new(r"\(#(?P<id>\d+)\)").unwrap(),
        }
    }
}

impl TodoChecker {
    pub fn run(&self) -> SingleStatusResult {
        let file = std::fs::File::open(&self.path).expect("could not open file");
        let mut results = Vec::new();
        let reader = BufReader::new(file);
        for (i, possible_line) in reader.lines().enumerate() {
            let line = match possible_line {
                Ok(line) => line,
                Err(_) => {
                    // Skip files that don't look like UTF-8.
                    results.push(SingleStatusResult {
                        value: StatusResultValue::Skipped,
                        logs: "".to_string(),
                    });
                    break;
                }
            };

            results.push(self.check_line(&line, i + 1));
        }
        status_combine(results.into_iter())
    }

    fn check_line(&self, line: &str, line_number: usize) -> SingleStatusResult {
        let mut logs = Vec::new();
        let mut result = StatusResultValue::Ok;
        if let Some(captures) = self.todo_re.captures(&line) {
            if let Some(details) = captures.name("details") {
                if let Some(captures) = self.details_re.captures(details.as_str()) {
                    let issue = captures.name("id").unwrap();
                    // TODO: check that this issue is currently open
                    let _issue = issue.as_str().parse::<u32>().unwrap();
                } else {
                    logs.push(format!(
                        "{}:{}: {}DO with malformed issue details",
                        self.path.to_str().unwrap(),
                        line_number,
                        "TO"
                    ));
                    result = StatusResultValue::Error;
                }
            } else {
                logs.push(format!(
                    "{}:{}: {}DO missing issue details",
                    self.path.to_str().unwrap(),
                    line_number,
                    "TO"
                ));
                result = StatusResultValue::Error;
            }
        }
        SingleStatusResult {
            value: result,
            logs: logs.join("\n"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::internal::{SingleStatusResult, StatusResultValue};

    #[test]
    fn test_non_matches() {
        let checker = TodoChecker::new(&std::path::Path::new("no-file").to_path_buf());
        let ok = SingleStatusResult {
            value: StatusResultValue::Ok,
            logs: "".to_string(),
        };
        assert_eq!(ok, checker.check_line("// comment", 42));
        assert_eq!(ok, checker.check_line("// TDO: not quite", 42));
    }

    #[test]
    fn test_no_number() {
        let checker = TodoChecker::new(&std::path::Path::new("no-file").to_path_buf());
        let fail = SingleStatusResult {
            value: StatusResultValue::Error,
            logs: format!("no-file:42: {}DO missing issue details", "TO"),
        };
        assert_eq!(
            fail,
            checker.check_line(&format!("// {}DO: no number", "TO"), 42)
        );
        assert_eq!(
            fail,
            checker.check_line(&format!("# {}DO: no number", "TO"), 42)
        );
    }

    #[test]
    fn test_malformed_number() {
        let checker = TodoChecker::new(&std::path::Path::new("no-file").to_path_buf());
        assert_eq!(
            SingleStatusResult {
                value: StatusResultValue::Error,
                logs: format!("no-file:42: {}DO with malformed issue details", "TO"),
            },
            checker.check_line(&format!("// TO{}(123): no hash", "DO"), 42)
        );
    }
}
