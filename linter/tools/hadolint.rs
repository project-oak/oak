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

pub struct HadolintTool {}

impl linter::LinterTool for HadolintTool {
    const NAME: &'static str = "Hadolint";

    fn accept(&self, path: &Path) -> anyhow::Result<bool> {
        Ok(super::has_extension(path, &["Dockerfile"])
            || super::has_filename(path, &["Dockerfile"]))
    }

    fn check(&self, path: &Path) -> anyhow::Result<linter::Outcome> {
        // Ignore Invalid Label Keys (DL3048), which is currently triggered by
        // underscored in Dockerfile labels. But underscores are specified in
        // the Confidential Space [documentation](https://cloud.google.com/confidential-computing/confidential-space/docs/reference/launch-policies)
        // and are also allowed in Docker format [recommendations](https://docs.docker.com/engine/manage-resources/labels/#key-format-recommendations).
        super::linter_command("hadolint", &["--ignore", "DL3048"], path)
    }
}
