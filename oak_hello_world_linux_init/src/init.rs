//
// Copyright 2023 The Project Oak Authors
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

/// Performs the minimum initialization required from the initial process on
/// Linux to allow an application on an initial RAM disk to operate as expected.
///
/// This will eventually become a shared library to support more general
/// workloads. For now we just do the minimum required to be able to run this
/// Hello World application, which is nothing.
pub fn init() -> anyhow::Result<()> {
    // We don't need to do any initialization to just log to the console, so this is
    // a placeholder for now. In future we will do basic initialization here:
    //
    // - Create mount points for pseudo file systems.
    // - Mount pseudo file systems.
    // - Create virtual files.
    //
    // See e.g. <http://git.2f30.org/fs/file/bin/rc.init.html> for an example initialization
    // script.

    Ok(())
}
