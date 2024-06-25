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

use std::{path::Path, process, sync::mpsc};

use ignore::{DirEntry, WalkBuilder};

// A mode flag to specify whether a linter run should just report errors, or
// also try to fix them in place.
#[derive(Copy, Clone, Debug)]
pub enum Mode {
    // When running the linter tool, only report errors, don't change the file.
    Check,

    // Fix any linter issues that the related tool is able to fix.
    Fix,
}

// The result of running a linter tool on a file.
// This may look like it should be a result, but "Failures" are not really
// errors in this context, so it remains its own type.
#[derive(Clone, Debug)]
pub enum Outcome {
    /// The linter action succeeded without issues
    Success,

    /// The linter tool failed to launch or failed to terminate normally.
    Failure(String),
}

// A tuple struct holding a filename, and the outcome for that filename.
#[derive(Debug)]
pub struct FileOutcome {
    pub filename: String,
    pub outcome: anyhow::Result<Outcome>,
}

/// An implementation of a linter tool.
pub trait LinterTool: Send + Sync {
    /// A display name for this tool.
    const NAME: &'static str;

    /// Return true if this tool can support any sort of automatic fixing
    /// behavior.
    const SUPPORTS_FIX: bool = false;

    /// Returns true if the provided [Path] appears to be a filetype handled by
    /// this tool. If there's an error making the determination, an Error result
    /// will be returned instead.
    fn accept(&self, entry: &Path) -> anyhow::Result<bool>;

    /// Run the linter tool in "check" mode - no changes will be made to the
    /// fail, but information about issues will be provided, if there are any.
    fn check(&self, entry: &Path) -> anyhow::Result<Outcome>;

    /// Run the linter tool in "fix" mode - when possible, the file issues will
    /// be automatically fixed in place. Note that not all tools can fix all
    /// issues, so some failure output may still occur.
    ///
    /// If fixing is not supported, this simply runs the check behavior.
    fn fix(&self, entry: &Path) -> anyhow::Result<Outcome> {
        self.check(entry)
    }
}

/// It's common to use a command line tool for linting.
/// This is a convenience to convert the output of the linter program into the
/// [Outcome] type returned from the linter.
///
/// In failure cases, stderr will be included as the output.
impl TryFrom<&mut process::Command> for Outcome {
    type Error = anyhow::Error;

    fn try_from(command: &mut process::Command) -> Result<Outcome, Self::Error> {
        let output = command.output()?;
        Ok(match output.status.success() {
            true => Outcome::Success,
            false => Outcome::Failure(format!(
                "{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            )),
        })
    }
}

// A structure that actually performs the linting on a group of files, via the
// `lint_files` method.
pub struct Linter<LT: LinterTool> {
    tool: LT,
}

impl<LT: LinterTool> Linter<LT> {
    // Create a new linter instance that uses the provided `tool` when
    // `lint_files` is called.
    pub fn new(tool: LT) -> Self {
        Linter { tool }
    }

    // Returns the [LinterTool] that this instance was constructed with.
    pub fn tool(&self) -> &LT {
        &self.tool
    }

    /// Lint one individual file with the [LinterTool],
    fn lint_file(&self, path: &Path, mode: Mode) -> Option<FileOutcome> {
        let accept = self.tool.accept(path).unwrap_or_else(|err| {
            eprintln!("Failed to check {} for acceptance: {err:?}", path.display(),);
            false
        });
        if accept {
            Some(FileOutcome {
                filename: path.display().to_string(),
                outcome: match mode {
                    Mode::Check => self.tool.check(path),
                    Mode::Fix => self.tool.fix(path),
                },
            })
        } else {
            None
        }
    }

    // Run the [LinterTool] on all of the files exposed by the provided
    // `WalkBuilder`, in the [Mode] specified.
    //
    // The files will be processed in parallel, with a thread count based on the
    // configuration of the provided WalkBuilder.
    pub fn lint_files(&self, walk_builder: &WalkBuilder, mode: Mode) -> Vec<FileOutcome> {
        let (tx, rx) = mpsc::channel();

        let is_directory =
            |entry: &DirEntry| entry.file_type().map(|ft| ft.is_dir()).unwrap_or(false);

        walk_builder.build_parallel().run(|| {
            Box::new(|entry| {
                match entry {
                    Ok(entry) if is_directory(&entry) => {}
                    Ok(entry) => {
                        if let Some(outcome) = self.lint_file(entry.path(), mode) {
                            tx.send(outcome).unwrap()
                        }
                    }
                    Err(err) => eprintln!("Failed to process something: {err:?}"),
                };
                ignore::WalkState::Continue
            })
        });

        // Drop the tx channel so that rx collection terminates.
        drop(tx);
        rx.iter().collect()
    }
}
