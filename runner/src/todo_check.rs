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
use lazy_static::lazy_static;
use log::warn;
use regex::Regex;
use serde::Deserialize;
use std::{
    collections::HashMap,
    io::{BufRead, BufReader, Read},
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

            // Only check GitHub issue status if it's available.
            results.push(self.check_line(&line, i + 1, issue_data_available()));
        }
        status_combine(results.into_iter())
    }

    fn check_line(&self, line: &str, line_number: usize, check_status: bool) -> SingleStatusResult {
        let mut logs = Vec::new();
        let mut result = StatusResultValue::Ok;
        if let Some(captures) = self.todo_re.captures(&line) {
            if let Some(details) = captures.name("details") {
                if let Some(captures) = self.details_re.captures(details.as_str()) {
                    if check_status {
                        let issue = captures
                            .name("id")
                            .unwrap()
                            .as_str()
                            .parse::<u32>()
                            .unwrap();
                        match issue_info(issue) {
                            None => {
                                logs.push(format!(
                                    "{}:{}: {}DO with issue number {} unknown at GitHub",
                                    self.path.to_str().unwrap(),
                                    line_number,
                                    "TO",
                                    issue
                                ));
                                result = StatusResultValue::Error;
                            }
                            Some(info) => {
                                if info.state != "open" {
                                    logs.push(format!(
                                        "{}:{}: {}DO with issue number {} marked closed at GitHub",
                                        self.path.to_str().unwrap(),
                                        line_number,
                                        "TO",
                                        issue
                                    ));
                                    result = StatusResultValue::Error;
                                }
                            }
                        }
                    }
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

#[derive(Clone, Debug, Deserialize)]
struct IssueInfo {
    number: u32,
    title: String,
    state: String,
}

lazy_static! {
    // GitHub API is rate limited so ensure we only get the list of issues once.
    static ref ISSUE_INFO: Option<HashMap<u32, IssueInfo>> = get_github_issues();
}

fn issue_data_available() -> bool {
    ISSUE_INFO.is_some()
}

fn issue_info(id: u32) -> Option<IssueInfo> {
    if let Some(info_map) = &*ISSUE_INFO {
        if let Some(info) = info_map.get(&id) {
            Some(info.clone())
        } else {
            None
        }
    } else {
        None
    }
}

// Get raw JSON issues from the given url. Returns the JSON body if found, and a next URL.
fn get_issues_from(url: &str) -> (Option<String>, Option<String>) {
    let mut rsp = match reqwest::blocking::Client::builder()
        .user_agent("rust-reqwest")
        .build()
        .unwrap()
        .get(url)
        .send()
    {
        Ok(rsp) => rsp,
        Err(err) => {
            warn!("Failed to retrieve issues from GitHub: {:?}", err);
            return (None, None);
        }
    };

    let mut next = None;
    let mut body = String::new();
    rsp.read_to_string(&mut body).unwrap();
    if rsp.status().is_success() {
        // Look for a 'next' entry in the link header.
        if let Ok(link_map) =
            parse_link_header::parse(rsp.headers()[reqwest::header::LINK].to_str().unwrap())
        {
            if let Some(link) = link_map.get(&Some("next".to_string())) {
                next = Some(link.raw_uri.clone());
            }
        }
        (Some(body), next)
    } else {
        warn!(
            "Failed to retrieve issues from GitHub, status {:?}",
            rsp.status()
        );
        (None, next)
    }
}

fn get_github_issues() -> Option<HashMap<u32, IssueInfo>> {
    let mut info_map = HashMap::new();
    let mut next_url = Some(
        "https://api.github.com/repos/project-oak/oak/issues?per_page=100&state=all".to_string(),
    );

    while let Some(url) = next_url {
        let (json_data, next) = get_issues_from(&url);
        if json_data.is_none() {
            warn!(
                "No JSON data from {:?}, GitHub issue checking unavailable",
                url
            );
            return None;
        };
        let values: Vec<IssueInfo> = match serde_json::from_str(&json_data.unwrap()) {
            Ok(v) => v,
            Err(err) => {
                warn!("Failed to parse JSON from GitHub: {:?}", err);
                return None;
            }
        };
        for info in values {
            info_map.insert(info.number, info);
        }
        next_url = next;
    }
    Some(info_map)
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
        assert_eq!(ok, checker.check_line("// comment", 42, false));
        assert_eq!(ok, checker.check_line("// TDO: not quite", 42, false));
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
            checker.check_line(&format!("// {}DO: no number", "TO"), 42, false),
        );
        assert_eq!(
            fail,
            checker.check_line(&format!("# {}DO: no number", "TO"), 42, false),
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
            checker.check_line(&format!("// TO{}(123): no hash", "DO"), 42, false)
        );
    }
}
