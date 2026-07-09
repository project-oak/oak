//
// Copyright 2025 The Project Oak Authors
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

//! Terminal report rendering with ANSI colors and version update analysis.

use std::{
    io::{self, Write},
    path::Path,
};

use colored::{Color, ColoredString, Colorize};
use semver::Version;

use crate::{
    CrateData, CrateVersionInfo,
    parse::{parse_version_lenient, strip_metadata},
};

// ── Column definitions ──────────────────────────────────────────────────────

/// Static properties of a report column.
struct ColInfo {
    header: &'static str,
    width: usize,
    truncate: bool,
}

/// Report columns. Adding a variant here forces handling in `info()` and
/// `Row::cell()` — the compiler won't let you forget.
#[derive(Clone, Copy)]
enum Col {
    Name,
    Requested,
    Actual,
    Patch,
    Minor,
    Major,
    Usage,
    Date,
}

impl Col {
    /// All columns in display order.
    const ALL: &[Col] = &[
        Col::Name,
        Col::Requested,
        Col::Actual,
        Col::Patch,
        Col::Minor,
        Col::Major,
        Col::Usage,
        Col::Date,
    ];

    fn info(self) -> ColInfo {
        match self {
            Col::Name => ColInfo { header: "Crate", width: 25, truncate: true },
            Col::Requested => ColInfo { header: "Req", width: 10, truncate: false },
            Col::Actual => ColInfo { header: "Act", width: 12, truncate: false },
            Col::Patch => ColInfo { header: "Latest(P)", width: 10, truncate: false },
            Col::Minor => ColInfo { header: "Latest(m)", width: 10, truncate: false },
            Col::Major => ColInfo { header: "Latest(M)", width: 10, truncate: false },
            Col::Usage => ColInfo { header: "Usage", width: 5, truncate: false },
            Col::Date => ColInfo { header: "Latest Date", width: 12, truncate: false },
        }
    }

    /// Format a value for this column with the given style and optional
    /// row-level background highlight.
    fn format(self, val: &str, fg: Option<Color>, bold: bool, highlight: bool) -> ColoredString {
        let ci = self.info();
        let mut s = val.to_string();
        if ci.truncate && s.len() > ci.width {
            s.truncate(ci.width.saturating_sub(3));
            s.push_str("...");
        }
        let padded = format!("{:<width$}", s, width = ci.width);
        let mut styled = if bold { padded.bold() } else { padded.normal() };
        if let Some(c) = fg {
            styled = styled.color(c);
        }
        if highlight {
            styled = styled.on_black();
        }
        styled
    }
}

fn separator_width() -> usize {
    Col::ALL.iter().map(|c| c.info().width).sum::<usize>() + Col::ALL.len() * 3 - 1
}

// ── Row rendering ────────────────────────────────────────────────────────────

/// Style for a cell: optional foreground color and bold flag.
#[derive(Clone, Copy, Default)]
struct Style {
    fg: Option<Color>,
    bold: bool,
}

impl Style {
    const NORMAL: Style = Style { fg: None, bold: false };
    const BOLD_RED: Style = Style { fg: Some(Color::BrightRed), bold: true };

    fn from_date(date_str: &str) -> Style {
        match color_for_date(date_str) {
            Some(c) => Style { fg: Some(c), bold: false },
            None => Style::NORMAL,
        }
    }
}

/// A single row of the crate report. Fields default to empty/NORMAL so
/// callers only need to set the fields they care about.
#[derive(Clone, Copy, Default)]
struct Row<'a> {
    name: &'a str,
    requested: &'a str,
    actual: &'a str,
    actual_style: Style,
    patch: &'a str,
    minor: &'a str,
    major: &'a str,
    usage: &'a str,
    date: &'a str,
    date_style: Style,
}

impl Row<'_> {
    /// Get the (value, style) pair for a given column.
    fn cell(&self, col: Col) -> (&str, Style) {
        match col {
            Col::Name => (self.name, Style::NORMAL),
            Col::Requested => (self.requested, Style::NORMAL),
            Col::Actual => (self.actual, self.actual_style),
            Col::Patch => (self.patch, Style::NORMAL),
            Col::Minor => (self.minor, Style::NORMAL),
            Col::Major => (self.major, Style::NORMAL),
            Col::Usage => (self.usage, Style::NORMAL),
            Col::Date => (self.date, self.date_style),
        }
    }

    /// Render the row as a formatted, optionally highlighted string.
    fn render(&self, highlight: bool) -> String {
        let parts: Vec<String> = Col::ALL
            .iter()
            .map(|col| {
                let (val, style) = self.cell(*col);
                col.format(val, style.fg, style.bold, highlight).to_string()
            })
            .collect();

        let sep = if highlight { " | ".on_black().to_string() } else { " | ".to_string() };
        parts.join(&sep)
    }
}

// ── Version helpers ──────────────────────────────────────────────────────────

/// Available version updates for a crate.
struct Updates {
    patch: Option<Version>,
    minor: Option<Version>,
    major: Option<Version>,
}

/// Find the latest Patch, Minor, and Major updates relative to `actual`.
fn find_latest_updates(actual: &Version, all_versions: &[Version]) -> Updates {
    let mut updates = Updates { patch: None, minor: None, major: None };

    for v in all_versions {
        if v <= actual {
            continue;
        }
        let slot = if v.major > actual.major {
            &mut updates.major
        } else if v.minor > actual.minor {
            &mut updates.minor
        } else {
            &mut updates.patch
        };
        if slot.as_ref().is_none_or(|existing| v > existing) {
            *slot = Some(v.clone());
        }
    }

    updates
}

/// Format an `Option<Version>` as a display string, stripping metadata.
fn version_or_dash(v: Option<Version>) -> String {
    v.map(|v| strip_metadata(&v.to_string()).to_string()).unwrap_or_else(|| "-".to_string())
}

/// Filter crates.io version info: exclude yanked, optionally exclude
/// pre-release.
fn filter_versions(
    versions: &[CrateVersionInfo],
    include_pre_release: bool,
) -> Vec<&CrateVersionInfo> {
    let mut filtered: Vec<_> = versions.iter().filter(|info| !info.yanked).collect();
    if !include_pre_release {
        filtered.retain(|info| {
            parse_version_lenient(&info.version).map(|sv| sv.pre.is_empty()).unwrap_or(true)
        });
    }
    filtered
}

/// Find the latest version string and its publication date from version info.
fn latest_version_info(
    versions_info: &[&CrateVersionInfo],
    all_versions: &[Version],
) -> (String, String) {
    let abs_latest = all_versions.iter().max();
    let latest_str = version_or_dash(abs_latest.cloned());

    let date_str = abs_latest
        .and_then(|latest| {
            versions_info.iter().find_map(|info| {
                let sv = semver::Version::parse(&info.version).ok()?;
                if &sv == latest {
                    Some(info.created_at.split('T').next().unwrap_or("-").to_string())
                } else {
                    None
                }
            })
        })
        .unwrap_or_else(|| "-".to_string());

    (latest_str, date_str)
}

// ── Date helpers ─────────────────────────────────────────────────────────────

const TWO_YEARS_SECS: i64 = 2 * 365 * 86400;
const THREE_YEARS_SECS: i64 = 3 * 365 * 86400;

/// Calculate the age of a "YYYY-MM-DD" date string in seconds.
fn date_age_secs(date_str: &str) -> Option<i64> {
    let naive_date = chrono::NaiveDate::parse_from_str(date_str, "%Y-%m-%d").ok()?;
    let dur =
        chrono::Utc::now().naive_utc().signed_duration_since(naive_date.and_hms_opt(0, 0, 0)?);
    Some(dur.num_seconds())
}

/// Choose a color based on how old a date is.
fn color_for_date(date_str: &str) -> Option<Color> {
    date_age_secs(date_str).and_then(|age_secs| {
        if age_secs > THREE_YEARS_SECS {
            Some(Color::BrightRed)
        } else if age_secs > TWO_YEARS_SECS {
            Some(Color::Yellow)
        } else {
            None
        }
    })
}

/// Format a duration in seconds into a human-readable string.
pub fn format_age(seconds: u64) -> String {
    match seconds {
        0..60 => format!("{}s", seconds),
        60..3600 => format!("{}m", seconds / 60),
        3600..86400 => format!("{}h", seconds / 3600),
        _ => format!("{}d", seconds / 86400),
    }
}

// ── Report entry point ───────────────────────────────────────────────────────

/// Print the full crate version report to stdout.
pub fn print_report(
    data: &[&CrateData],
    total_count: usize,
    include_pre_release: bool,
    versions_path: Option<&Path>,
    cache_age_secs: Option<u64>,
) -> io::Result<()> {
    let out = io::stdout();
    let mut out = out.lock();

    print_header(&mut out)?;
    let displayed = print_rows(&mut out, data, include_pre_release)?;
    print_footer(&mut out, total_count, displayed, versions_path, cache_age_secs)
}

/// Print the column headers and separator line.
fn print_header(out: &mut impl Write) -> io::Result<()> {
    let header: Vec<String> = Col::ALL
        .iter()
        .map(|col| {
            let ci = col.info();
            col.format(ci.header, None, true, false).to_string()
        })
        .collect();
    writeln!(out, "{}", header.join(" | "))?;
    writeln!(out, "{}", "-".repeat(separator_width()))
}

/// Print all data rows, returning the number of rows actually displayed.
fn print_rows(
    out: &mut impl Write,
    data: &[&CrateData],
    include_pre_release: bool,
) -> io::Result<usize> {
    let mut displayed = 0;

    for (row_idx, entry) in data.iter().enumerate() {
        let requested = strip_metadata(&entry.requested);

        // Skip pre-release requested versions unless flag is set.
        if !include_pre_release
            && parse_version_lenient(requested).is_some_and(|v| !v.pre.is_empty())
        {
            continue;
        }
        displayed += 1;

        let mut actual_list: Vec<&Version> = entry.actual.iter().collect();
        if !include_pre_release {
            actual_list.retain(|v| v.pre.is_empty());
        }
        actual_list.sort();

        let highlight = row_idx % 2 == 1;
        let usage_str = entry.usage.to_string();

        // No actual version installed — print MISSING and move on.
        if actual_list.is_empty() {
            writeln!(
                out,
                "{}",
                Row {
                    name: &entry.name,
                    requested,
                    actual: "MISSING",
                    actual_style: Style::BOLD_RED,
                    usage: &usage_str,
                    ..Row::default()
                }
                .render(highlight)
            )?;
            continue;
        }

        // Gather crates.io version data for update comparison.
        let versions_info = filter_versions(&entry.versions, include_pre_release);
        let all_versions: Vec<Version> = versions_info
            .iter()
            .filter_map(|info| semver::Version::parse(&info.version).ok())
            .collect();

        let (_, latest_date_str) = latest_version_info(&versions_info, &all_versions);

        let highest = actual_list.iter().max().unwrap();
        let u = find_latest_updates(highest, &all_versions);

        let base_row = Row {
            name: &entry.name,
            requested,
            patch: &version_or_dash(u.patch),
            minor: &version_or_dash(u.minor),
            major: &version_or_dash(u.major),
            usage: &usage_str,
            date: &latest_date_str,
            date_style: Style::from_date(&latest_date_str),
            ..Row::default()
        };

        for (i, v) in actual_list.iter().enumerate() {
            let is_too_old =
                parse_version_lenient(requested).as_ref().map(|req| *v < req).unwrap_or(false);
            let v_str = strip_metadata(&v.to_string()).to_string();
            let actual = if is_too_old { format!("{} (<)", v_str) } else { v_str };
            let actual_style = if is_too_old { Style::BOLD_RED } else { Style::NORMAL };

            // First row shows all crate info; continuation rows are blank except actual.
            let defaults = if i == 0 { base_row } else { Row::default() };
            writeln!(
                out,
                "{}",
                (Row { actual: &actual, actual_style, ..defaults }).render(highlight)
            )?;
        }
    }

    Ok(displayed)
}

/// Print the summary footer.
fn print_footer(
    out: &mut impl Write,
    total_count: usize,
    displayed: usize,
    versions_path: Option<&Path>,
    cache_age_secs: Option<u64>,
) -> io::Result<()> {
    writeln!(out, "{}", "-".repeat(separator_width()))?;
    writeln!(out)?;
    writeln!(out, "Update Summary (Latest vs Actual):")?;
    writeln!(out, "  Latest dates colored by age: Yellow > 2yrs, Red > 3yrs")?;
    writeln!(out, "  Rows have alternating background shading.")?;

    if total_count != displayed {
        writeln!(out, "  Showing {} crates (filtered from {})", displayed, total_count)?;
    } else {
        writeln!(out, "  Total Crates Analyzed:     {}", displayed)?;
    }

    if let Some(vp) = versions_path {
        let age_str =
            cache_age_secs.map(|s| format!(" (updated {} ago)", format_age(s))).unwrap_or_default();
        writeln!(out)?;
        writeln!(out, "Versions Cache: {}{}", vp.display(), age_str)?;
        writeln!(out, "To update the cache, run with the --update or -u flag.")?;
    }

    Ok(())
}
