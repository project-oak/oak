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

use std::{env, fs, path::PathBuf};

fn kebab_to_camel(s: &str) -> String {
    let mut parts = s.split('-');
    let first = parts.next().unwrap_or_default().to_string();
    let rest: String = parts
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                Some(c) => c.to_ascii_uppercase().to_string() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect();
    first + &rest
}

fn kebab_to_pascal(s: &str) -> String {
    s.split('-')
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                Some(c) => c.to_ascii_uppercase().to_string() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect()
}

fn wit_type_to_ts(wit_type: &str) -> String {
    let trimmed = wit_type.trim();
    if let Some(inner) = trimmed.strip_prefix("list<").and_then(|s| s.strip_suffix('>')) {
        return format!("Array<{}>", wit_type_to_ts(inner));
    }
    if let Some(inner) = trimmed.strip_prefix("result<").and_then(|s| s.strip_suffix('>')) {
        let ok_type = inner.split(',').next().unwrap_or("void").trim();
        return wit_type_to_ts(ok_type);
    }
    match trimmed {
        "string" => "string".to_string(),
        "bool" => "boolean".to_string(),
        "u8" | "u16" | "u32" | "s8" | "s16" | "s32" | "f32" | "f64" => "number".to_string(),
        "u64" | "s64" => "bigint".to_string(),
        other => kebab_to_pascal(other),
    }
}

/// Generates TypeScript ambient module declarations for the `tools` interface
/// in `agent.wit`.
pub fn generate_ts_declarations(wit_src: &str) -> String {
    let mut package_name = String::new();
    let mut package_version = String::new();

    for line in wit_src.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("package ") {
            let pkg = rest.trim_end_matches(';').trim();
            if let Some((name, ver)) = pkg.split_once('@') {
                package_name = name.to_string();
                package_version = format!("@{ver}");
            } else {
                package_name = pkg.to_string();
            }
            break;
        }
    }

    let module_id = format!("{package_name}/tools{package_version}");

    let mut functions = Vec::new();
    let mut records = Vec::new();

    let mut in_tools_interface = false;
    let mut current_record: Option<(String, Vec<(String, String)>)> = None;

    for line in wit_src.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }

        if !in_tools_interface {
            if trimmed.starts_with("interface tools") && trimmed.ends_with('{') {
                in_tools_interface = true;
            }
            continue;
        }

        if let Some((ref rec_name, ref mut fields)) = current_record {
            if trimmed == "}" {
                records.push((rec_name.clone(), std::mem::take(fields)));
                current_record = None;
            } else if let Some((field_name, field_type)) =
                trimmed.trim_end_matches(',').split_once(':')
            {
                fields.push((kebab_to_camel(field_name.trim()), wit_type_to_ts(field_type.trim())));
            }
            continue;
        }

        if trimmed == "}" {
            break;
        }

        if let Some(rest) = trimmed.strip_prefix("record ") {
            let rec_name = rest.trim_end_matches('{').trim();
            current_record = Some((kebab_to_pascal(rec_name), Vec::new()));
        } else if let Some((fn_name, sig)) = trimmed.trim_end_matches(';').split_once(": func(")
            && let Some((params_str, ret_part)) = sig.split_once(')')
        {
            let params: Vec<String> = params_str
                .split(',')
                .filter(|s| !s.trim().is_empty())
                .map(|p| {
                    let (p_name, p_type) = p.split_once(':').expect("Invalid WIT param");
                    format!("{}: {}", kebab_to_camel(p_name.trim()), wit_type_to_ts(p_type))
                })
                .collect();
            let ret_type = ret_part
                .trim()
                .strip_prefix("->")
                .map(|r| wit_type_to_ts(r.trim()))
                .unwrap_or_else(|| "void".to_string());
            functions.push(format!(
                "  export function {}({}): {};",
                kebab_to_camel(fn_name.trim()),
                params.join(", "),
                ret_type
            ));
        }
    }

    let mut out = String::from(
        "// Copyright 2026 The Project Oak Authors\n\
         //\n\
         // Licensed under the Apache License, Version 2.0 (the \"License\");\n\
         // you may not use this file except in compliance with the License.\n\
         // You may obtain a copy of the License at\n\
         //\n\
         //     http://www.apache.org/licenses/LICENSE-2.0\n\
         //\n\
         // Unless required by applicable law or agreed to in writing, software\n\
         // distributed under the License is distributed on an \"AS IS\" BASIS,\n\
         // WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.\n\
         // See the License for the specific language governing permissions and\n\
         // limitations under the License.\n\n",
    );

    out.push_str(&format!("declare module '{module_id}' {{\n"));
    out.push_str(&format!("  /** @module Interface {module_id} **/\n"));
    for func in &functions {
        out.push_str(func);
        out.push('\n');
    }
    for (rec_name, fields) in &records {
        out.push_str(&format!("  export interface {rec_name} {{\n"));
        for (f_name, f_type) in fields {
            out.push_str(&format!("    {f_name}: {f_type};\n"));
        }
        out.push_str("  }\n");
    }
    out.push_str("}\n");
    out
}

fn main() {
    let wit_path = env!("WIT_FILE");
    let wit_src = fs::read_to_string(wit_path)
        .unwrap_or_else(|e| panic!("Failed to read WIT file at {wit_path}: {e}"));
    let generated = generate_ts_declarations(&wit_src);

    if let Ok(workspace_dir) = env::var("BUILD_WORKSPACE_DIRECTORY") {
        let out_path =
            PathBuf::from(workspace_dir).join("oak_trusted_agent/sandbox/agent_ts/src/types.d.ts");
        fs::write(&out_path, &generated)
            .unwrap_or_else(|e| panic!("Failed to write {}: {e}", out_path.display()));
        println!("Updated {}", out_path.display());
    } else {
        print!("{generated}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_types_d_ts_matches_wit() {
        let wit_path = env!("WIT_FILE");
        let checked_in_path = env!("CHECKED_IN_TYPES");

        let wit_src = fs::read_to_string(wit_path)
            .unwrap_or_else(|e| panic!("Failed to read WIT file at {wit_path}: {e}"));
        let checked_in = fs::read_to_string(checked_in_path)
            .unwrap_or_else(|e| panic!("Failed to read types.d.ts at {checked_in_path}: {e}"));

        let expected = generate_ts_declarations(&wit_src);

        assert_eq!(
            checked_in.trim(),
            expected.trim(),
            "\n\nERROR: oak_trusted_agent/sandbox/agent_ts/src/types.d.ts is out of sync with oak_trusted_agent/sandbox/wit/agent.wit!\n\
            To regenerate types.d.ts from agent.wit, run:\n\
            \n  bazel run //oak_trusted_agent/sandbox:generate_wit_types\n"
        );
    }
}
