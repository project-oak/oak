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

pub struct BuildifierTool {}

impl linter::LinterTool for BuildifierTool {
    const NAME: &'static str = "Buildifier";
    const SUPPORTS_FIX: bool = true;

    fn accept(&self, path: &Path) -> anyhow::Result<bool> {
        Ok(super::has_extension(path, &["bzl"])
            || super::has_filename(path, &["BUILD", "WORKSPACE"]))
    }

    fn check(&self, path: &Path) -> anyhow::Result<linter::Outcome> {
        super::linter_command("buildifier", &["-mode=check", "-lint=warn"], path)
    }

    fn fix(&self, path: &Path) -> anyhow::Result<linter::Outcome> {
        super::linter_command("buildifier", &["-mode=fix", "-lint=fix", "-v"], path)
    }
}
