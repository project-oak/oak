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

pub struct BuildFileLicenseTool {}

impl linter::LinterTool for BuildFileLicenseTool {
    const NAME: &'static str = "Build File License";

    fn accept(&self, path: &Path) -> anyhow::Result<bool> {
        Ok(super::has_filename(path, &["BUILD"]))
    }

    fn check(&self, path: &Path) -> anyhow::Result<linter::Outcome> {
        let f = File::open(path)?;

        for line in BufReader::new(f).lines().take(50) {
            if line?.contains(r#"licenses = ["notice"]"#) {
                return Ok(linter::Outcome::Success);
            }
        }
        Ok(linter::Outcome::Failure("No license file header found.".to_string()))
    }
}
