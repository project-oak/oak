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

use std::path::Path;

use super::has_extension;

pub struct PrettierTool {}

impl linter::LinterTool for PrettierTool {
    const NAME: &'static str = "Prettier";
    const SUPPORTS_FIX: bool = true;

    fn accept(&self, path: &Path) -> anyhow::Result<bool> {
        Ok(has_extension(path, &["yaml", "yml", "html", "htm", "js", "ts", "tsx", "msj"]))
    }

    fn check(&self, path: &Path) -> anyhow::Result<linter::Outcome> {
        super::linter_command("prettier", &["--check", "--log-level=warn"], path)
    }

    fn fix(&self, path: &Path) -> anyhow::Result<linter::Outcome> {
        super::linter_command("prettier", &["--write", "--log-level=warn"], path)
    }
}
