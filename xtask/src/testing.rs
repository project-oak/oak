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

use crate::internal::{read_to_end, Command, Context, Opt, Runnable, Running, Scope, Status, Step};

fn opt_for_test() -> Opt {
    Opt {
        dry_run: false,
        logs: true,
        keep_going: false,
        scope: Scope::All,
        cmd: Command::RunTests,
    }
}

/// Runs a step, and asserts that it succeeds.
pub async fn run_step(step: Step) {
    let context = Context::root(&opt_for_test());
    let run_status = Status::new(usize::MAX);
    let result = crate::internal::run_step(&context, step, run_status).await;
    assert!(result.success());
}

/// Runs a step in the background, and returns a reference to the running process.
///
/// The running process is NOT killed when the returned `Running` is dropped. It must be killed
/// manually.
pub async fn run_background(step: Box<dyn Runnable>) -> Box<dyn Running> {
    let mut running = step.run(&opt_for_test());
    tokio::spawn(read_to_end(running.stdout()));
    tokio::spawn(read_to_end(running.stderr()));
    running
}

/// Whether to skip the test. For instance, GitHub Actions does not support KVM, so we cannot run
/// tests that require nested virtualization.
pub fn skip_test() -> bool {
    std::env::var("OAK_KVM_TESTS")
        .unwrap_or_default()
        .to_lowercase()
        == "skip"
}
