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

//! Decodes and displays the in-toto Statement and Predicate from a signed
//! envelope.

use std::{
    io::{self, Write},
    path::PathBuf,
};

use anyhow::Result;
use clap::Parser;
use oak_trusted_agent_provenance_common::{envelope::Envelope, flags, statement::InTotoStatement};
use serde_json::Value;

#[derive(Parser)]
#[command(about = "Displays the in-toto Statement and Predicate inside a signed envelope")]
struct Args {
    /// The signed statement envelope to read.
    #[arg(long, value_parser = flags::parse_path)]
    statement: PathBuf,
}

fn format_scalar(v: &Value) -> String {
    match v {
        Value::String(s) => s.clone(),
        Value::Number(n) if n.is_f64() => {
            let f = n.as_f64().unwrap_or(0.0);
            format!("{}", (f * 10_000.0).round() / 10_000.0)
        }
        other => other.to_string(),
    }
}

fn format_predicate_entry(key: &str, value: &Value) -> String {
    match (key, value) {
        ("benchmark", Value::Object(map)) => {
            let name = map.get("name").and_then(Value::as_str).unwrap_or("");
            match map.get("version").and_then(Value::as_str) {
                Some(version) => format!("{name} {version}"),
                None => name.to_string(),
            }
        }
        ("model", Value::Object(map)) => {
            let name = map.get("name").and_then(Value::as_str).unwrap_or("");
            let mut attrs = Vec::new();
            if let Some(params) = map.get("parameters").and_then(Value::as_str) {
                attrs.push(params.to_string());
            }
            if let Some(quant) = map.get("quantization").and_then(Value::as_str) {
                attrs.push(quant.to_string());
            }
            if let Some(sampling) = map.get("sampling").and_then(Value::as_object) {
                for (k, v) in sampling {
                    attrs.push(format!("{k}={}", format_scalar(v)));
                }
            }
            if attrs.is_empty() {
                name.to_string()
            } else {
                format!("{name} ({})", attrs.join(", "))
            }
        }
        ("run", Value::Object(map)) => {
            let started = map.get("started_at").and_then(Value::as_str).unwrap_or("");
            let finished = map.get("finished_at").and_then(Value::as_str).unwrap_or("");
            format!("{started} → {finished}")
        }
        (_, other) => format_scalar(other),
    }
}

fn write_statement(statement: &InTotoStatement, w: &mut impl Write) -> io::Result<()> {
    let subjects: Vec<_> = statement
        .subject
        .iter()
        .flat_map(|subject| {
            subject
                .digest
                .iter()
                .map(move |(algorithm, hex)| (subject.name.as_str(), format!("{algorithm}:{hex}")))
        })
        .collect();
    let subject_width = subjects.iter().map(|(name, _)| name.len()).max().unwrap_or(0);

    writeln!(w, "── 📜 Statement {}", "─".repeat(64))?;
    writeln!(w, "  predicate type   {}", statement.predicate_type)?;
    for (name, digest) in &subjects {
        writeln!(w, "  subject          {name:<subject_width$}  {digest}")?;
    }

    if !statement.predicate.is_empty() {
        writeln!(w, "\n── 📊 Predicate {}", "─".repeat(64))?;
        for (key, value) in &statement.predicate {
            if key == "score" || key == "detail" {
                continue;
            }
            writeln!(w, "  {key:<15}  {}", format_predicate_entry(key, value))?;
        }
        if let Some(Value::Object(map)) = statement.predicate.get("detail") {
            let entries: Vec<_> = map
                .iter()
                .filter(|(k, _)| !matches!(k.as_str(), "suite" | "attack" | "trials" | "resisted"))
                .collect();
            if !entries.is_empty() {
                writeln!(w, "  detail")?;
                let last = entries.len() - 1;
                for (i, (k, v)) in entries.into_iter().enumerate() {
                    let branch = if i == last { "└──" } else { "├──" };
                    writeln!(w, "     {branch} {k:<20}  {}", format_scalar(v))?;
                }
            }
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let args = Args::parse();
    let envelope = Envelope::read(&args.statement)?;
    let (_, statement) = envelope.decode_payload()?;
    write_statement(&statement, &mut io::stdout().lock())?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use clap::CommandFactory;
    use oak_trusted_agent_provenance_common::statement::{self, Predicate};

    use super::*;

    #[test]
    fn the_command_line_is_well_formed() {
        Args::command().debug_assert();
    }

    #[test]
    fn reader_renders_statement_and_predicate() {
        let mut predicate = Predicate::new();
        predicate.insert(
            "benchmark".to_string(),
            serde_json::json!({"name": "agentdojo", "version": "v1.2.2"}),
        );
        predicate.insert("score".to_string(), serde_json::json!(0.75));
        predicate.insert(
            "detail".to_string(),
            serde_json::json!({
                "suite": "travel",
                "attack": "important_instructions",
                "trials": 140,
                "resisted": 139,
                "attack_success_rate": 0.007142857142857143,
                "utility_rate": 0.85
            }),
        );
        let signed = statement::new(
            vec![statement::subject("report.jsonl", b"passed")],
            "https://example.com/v1".to_string(),
            predicate,
        )
        .unwrap();

        let mut out = Vec::new();
        write_statement(&signed, &mut out).unwrap();
        let rendered = String::from_utf8(out).unwrap();
        assert!(rendered.contains(&format!("── 📜 Statement {}\n", "─".repeat(64))));
        assert!(rendered.contains(&format!(
            "── 📊 Predicate {}\n  benchmark        agentdojo v1.2.2\n  detail\n     ├── attack_success_rate   0.0071\n     └── utility_rate          0.85\n",
            "─".repeat(64)
        )));
        assert!(!rendered.contains("score"));
        assert!(!rendered.contains("suite"));
    }
}
