//
// Copyright 2026 The Project Oak Authors
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
    io::{self, IsTerminal, Write},
    time::Duration,
};

use colored::*;

use crate::{config::Tool, identify::FileWithTags, run::ToolResult};

/// Manages the terminal user interface for displaying progress and results.
pub struct Dashboard {
    /// The number of active tools being tracked.
    num_active: usize,
    /// Whether the output is an interactive terminal.
    is_terminal: bool,
}

impl Dashboard {
    /// Creates a new `Dashboard` and prints the initial status for all active
    /// tools.
    pub fn new(active: &[Tool], file_tags: &[FileWithTags]) -> Self {
        let is_terminal = io::stdout().is_terminal();
        for t in active {
            let count = file_tags.iter().filter(|f| t.matches(&f.path, &f.tags)).count();
            let files_text = format!("{:10} files  ", count);
            println!(
                "{}  {}  {}",
                format!("{:8}", "Running:").blue(),
                format_tool_name(t.display_name()).bold(),
                files_text.blue()
            );
        }
        Self { num_active: active.len(), is_terminal }
    }

    /// Returns the number of active tools.
    pub fn num_active(&self) -> usize {
        self.num_active
    }

    /// Updates the terminal output for a specific tool.
    ///
    /// If output is a terminal, it uses ANSI escape sequences to overwrite the
    /// line. Otherwise, it prints a new line with the status.
    pub fn update(
        &self,
        idx: usize,
        name: &str,
        success: bool,
        count: usize,
        dur: Duration,
    ) -> io::Result<()> {
        let mut stdout = io::stdout().lock();
        let display_name = format_tool_name(name);

        let status_text = if success { "Passed" } else { "Failed" };
        let status = if success {
            format!("{:8}", status_text).green()
        } else {
            format!("{:8}", status_text).red()
        };

        let files_text = format!("{:10} files ", count);
        let time_text = format!("{:10}", format!("{:.3}s", dur.as_secs_f64()));

        if self.is_terminal {
            let lines_up = self.num_active - idx;
            write!(stdout, "{}", "\x1B[A".repeat(lines_up))?;
            write!(stdout, "\x1B[2K\r")?;
            write!(
                stdout,
                "{}  {}  {}  {}",
                status.bold(),
                display_name.bold(),
                files_text.color(if success { Color::Green } else { Color::Red }),
                time_text.color(get_time_color(dur))
            )?;
            write!(stdout, "{}", "\x1B[B".repeat(lines_up))?;
            write!(stdout, "\r")?;
        } else {
            writeln!(stdout, "{}  {}  {}  {}", status, display_name, files_text, time_text)?;
        }
        stdout.flush()
    }
}

/// Returns a color based on the duration, with red being "slow" and cyan being
/// "fast".
pub fn get_time_color(d: Duration) -> Color {
    let s = d.as_secs_f32();
    if s < 0.5 {
        Color::Cyan
    } else if s < 2.0 {
        Color::Green
    } else if s < 5.0 {
        Color::Yellow
    } else {
        Color::Red
    }
}

/// Prints a list of tools that were skipped because no files matched their
/// criteria.
pub fn print_skipped(skipped: &[Tool]) {
    if !skipped.is_empty() {
        println!("{}", "Skipped (no matching files):".dimmed());
        for t in skipped {
            println!("  {}", t.display_name().dimmed());
        }
        println!();
    }
}

/// Reports a summary of the linting results.
pub fn report_summary(results: &[ToolResult], total_dur: Duration) {
    let mut failures = Vec::new();

    for res in results {
        if !res.success {
            failures.push((&res.name, &res.output));
        }
    }

    println!(
        "\n{} {}",
        "Total time:".bold(),
        format!("{:.3}s", total_dur.as_secs_f64()).color(get_time_color(total_dur))
    );

    for (name, out) in failures {
        println!(
            "\n{} {}\n{}",
            "--- Failure Details:".red().bold(),
            name.red().bold(),
            out.trim().lines().map(|l| format!("    {}", l.red())).collect::<Vec<_>>().join("\n")
        );
    }
}

/// Formats a tool name for display in the UI.
fn format_tool_name(name: &str) -> String {
    format!("{:40}", name.chars().take(40).collect::<String>())
}
