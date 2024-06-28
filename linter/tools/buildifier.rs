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
            .and_then(|outcome| process_fix_warnings(self, path, outcome))
    }
}

// The buildifer verbose output is noisy, and provides a lot of useless
// information. The interesting bits are that sometimes fix can't fix anything,
// and reports remaining warnings. But it doesn't tell you what they are. So in
// those cases, we should run check again, and report the warnings.
fn process_fix_warnings<T: linter::LinterTool>(
    tool: &T,
    path: &Path,
    outcome: linter::Outcome,
) -> anyhow::Result<linter::Outcome> {
    match outcome {
        // It was fixed, no issues.
        linter::Outcome::Success(msg) if msg.contains("0 warnings left") => {
            Ok(linter::Outcome::Success("".to_string()))
        }
        // It was fixed, but issues remain. Run normal check to show them.
        linter::Outcome::Success(_) => tool.check(path),
        // It failed, so just show those results.
        linter::Outcome::Failure(_) => Ok(outcome),
    }
}
