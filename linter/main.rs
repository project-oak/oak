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

use std::{io::Write, time::Instant};

use clap::Parser;
use colored::*;
use linter::Linter;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    // Set to true to attempt to automatically fix issues.
    #[arg(short, long)]
    fix: bool,

    // If true, includes more output, like listing succeeded files.
    #[arg(short, long)]
    verbose: bool,

    // The root directory to search for files in. Defaults to `.`.
    #[arg(short, long, default_value = ".")]
    root: String,
}

struct LinterContext {
    walk_builder: ignore::WalkBuilder,
    mode: linter::Mode,
    verbose: bool,
}

#[derive(Clone, Debug, Default)]
struct ResultCounts {
    processed: usize,
    error_messages: Vec<String>,
}

impl std::ops::AddAssign<ResultCounts> for ResultCounts {
    fn add_assign(&mut self, rhs: ResultCounts) {
        self.processed += rhs.processed;
        self.error_messages.extend(rhs.error_messages);
    }
}

fn main() {
    let args = Args::parse();
    let mode = if args.fix { linter::Mode::Fix } else { linter::Mode::Check };

    let mut walk_builder = ignore::WalkBuilder::new(args.root);
    walk_builder.threads(100);
    walk_builder.add_ignore(".lintignore");

    let context = LinterContext { walk_builder, mode, verbose: args.verbose };

    let start = Instant::now();
    let mut counts = ResultCounts::default();

    counts += context.lint(tools::bad_todos::BadTodoTool {});
    counts += context.lint(tools::build_license::BuildFileLicenseTool {});
    counts += context.lint(tools::buildifier::BuildifierTool {});
    counts += context.lint(tools::clang_format::ClangFormatTool {});
    counts += context.lint(tools::hadolint::HadolintTool {});
    counts += context.lint(tools::ktfmt::KtfmtTool {});
    counts += context.lint(tools::prettier::PrettierTool {});
    counts += context.lint(tools::shell_check::ShellCheckTool {});
    counts += context.lint(tools::terraform::TerraformFmtTool {});
    counts += context.lint(tools::rustfmt::RustfmtTool {});
    counts += context.lint(tools::markdownlint::MarkdownlintTool {});
    counts += context.lint(tools::source_license::SourceLicenseTool {});

    let end = Instant::now();
    let elapsed = end.duration_since(start);
    println!("\n\nProcessed {} files in {:?}", counts.processed, elapsed);

    if !counts.error_messages.is_empty() {
        println!("{}", format!("Files with issues: {}", counts.error_messages.len()).red());
        for message in counts.error_messages {
            println!("{}", message.red());
        }
        std::process::exit(1);
    } else {
        println!("{}", "No files with issues found".cyan());
        std::process::exit(0);
    }
}

impl LinterContext {
    fn banner<LT: linter::LinterTool>(&self) {
        let verb = match self.mode {
            linter::Mode::Fix if LT::SUPPORTS_FIX => "Fixing".cyan(),
            _ => "Checking".green(),
        };
        let title = format!("{} {}", verb, LT::NAME.bright_white());

        print!("======>{title}... ");
        let _ = std::io::stdout().flush();
    }

    fn lint<LT: linter::LinterTool>(&self, tool: LT) -> ResultCounts {
        let start = Instant::now();
        self.banner::<LT>();
        let linter = Linter::new(tool);
        let outcomes = linter.lint_files(&self.walk_builder, self.mode);
        let processed = outcomes.len();
        let mut error_messages = Vec::new();
        for outcome in outcomes {
            match outcome.outcome {
                Err(err) => {
                    let message = format!("TOOL FAILURE {err:?}").red();
                    println!("{}", message);
                    error_messages.push(format!("{}: {}", outcome.filename, message));
                }
                Ok(linter::Outcome::Success(message)) => {
                    if !message.is_empty() {
                        println!("{}", message);
                    }
                    if self.verbose {
                        println!("No issues: {}", outcome.filename.cyan())
                    }
                }
                Ok(linter::Outcome::Failure(message)) => {
                    error_messages.push(format!("{}: {}", outcome.filename, message));
                }
            };
        }
        let end = Instant::now();
        let elapsed = end.duration_since(start);
        let error_count = error_messages.len();
        let summary = if error_count > 0 {
            let issue_word = if error_count == 1 { "issue" } else { "issues" };
            format!("{error_count} {issue_word} found").red()
        } else {
            "no issues found".to_string().truecolor(0, 200, 0)
        };
        println!("{summary}. processed {} files in {:?}", processed, elapsed);
        ResultCounts { processed, error_messages }
    }
}
