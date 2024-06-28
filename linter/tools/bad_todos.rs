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

use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

use lazy_static::lazy_static;
use linter::Outcome;
use regex::Regex;

pub struct BadTodoTool {}

lazy_static! {
    // Using \x54 = T to prevent triggering the lint here.
    static ref PATTERN: Regex = Regex::new("(\x54ODO\\(#[0-9]+\\)|\x54ODO: .+ - [0-9A-Za-z]+)")
        .expect("couldn't parse regex");
}

fn is_invalid_todo(line: &str) -> bool {
    // Using \x54 = T to prevent triggering the lint here.
    line.contains("\x54ODO") && !PATTERN.is_match(line)
}

impl linter::LinterTool for BadTodoTool {
    // Using \x54 = T to prevent triggering the lint here.
    const NAME: &'static str = "Bad \x54ODOs";

    fn accept(&self, path: &Path) -> anyhow::Result<bool> {
        Ok(super::has_extension(path, &["c", "h", "cc", "java", "go", "js", "proto", "kt", "rs"]))
    }

    fn check(&self, path: &Path) -> anyhow::Result<Outcome> {
        let f = File::open(path)?;
        let reader = BufReader::new(f);

        let mut results = Vec::<String>::new();
        for (n, line) in reader.lines().enumerate() {
            let line = line?;
            if is_invalid_todo(&line) {
                results.push(format!(" . Line {}: {}", n, line));
            }
        }

        Ok(if results.is_empty() {
            Outcome::Success("".to_string())
        } else {
            Outcome::Failure(results.join("\n"))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::is_invalid_todo;

    #[test]
    fn check_todos() {
        // Using \x54 = T to prevent triggering the lint here.
        assert!(is_invalid_todo("\x54ODO()"));
        assert!(!is_invalid_todo("\x54ODO(#123)"));

        assert!(!is_invalid_todo("\x54ODO: b/123 - do something."));
        // Missing link separator.
        assert!(is_invalid_todo("\x54ODO: do something."));
        // Empty link.
        assert!(is_invalid_todo("\x54ODO: - do something."));
        assert!(is_invalid_todo("\x54ODO:-do something."));
        // Empty description.
        assert!(is_invalid_todo("\x54ODO: b/123 - ."));
        assert!(is_invalid_todo("\x54ODO: b/123 -."));
    }
}
