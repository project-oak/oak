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

use std::{collections::HashSet, env, fs, path::PathBuf};

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

struct WitInterface {
    name: String,
    functions: Vec<String>,
    records: Vec<(String, Vec<(String, String)>)>,
    enums: Vec<(String, Vec<String>)>,
}

/// Generates TypeScript ambient module declarations for interfaces in
/// `agent.wit`.
pub fn generate_ts_declarations(wit_src: &str) -> String {
    let mut package_name = String::new();
    let mut package_version = String::new();
    let mut imported_interfaces = HashSet::new();

    let mut in_world = false;
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
        } else if trimmed.starts_with("world ") && trimmed.ends_with('{') {
            in_world = true;
        } else if in_world {
            if trimmed == "}" {
                in_world = false;
            } else if let Some(rest) = trimmed.strip_prefix("import ") {
                let iface = rest.trim_end_matches(';').trim();
                imported_interfaces.insert(iface.to_string());
            }
        }
    }

    let mut interfaces: Vec<WitInterface> = Vec::new();
    let mut current_interface: Option<WitInterface> = None;
    let mut current_record: Option<(String, Vec<(String, String)>)> = None;
    let mut current_enum: Option<(String, Vec<String>)> = None;

    for line in wit_src.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }

        if let Some(ref mut iface) = current_interface {
            if let Some((ref enum_name, ref mut cases)) = current_enum {
                if trimmed == "}" {
                    iface.enums.push((enum_name.clone(), std::mem::take(cases)));
                    current_enum = None;
                } else {
                    let case = trimmed.trim_end_matches(',').trim();
                    if !case.is_empty() {
                        cases.push(case.to_string());
                    }
                }
                continue;
            }

            if let Some((ref rec_name, ref mut fields)) = current_record {
                if trimmed == "}" {
                    iface.records.push((rec_name.clone(), std::mem::take(fields)));
                    current_record = None;
                } else if let Some((field_name, field_type)) =
                    trimmed.trim_end_matches(',').split_once(':')
                {
                    fields.push((
                        kebab_to_camel(field_name.trim()),
                        wit_type_to_ts(field_type.trim()),
                    ));
                }
                continue;
            }

            if trimmed == "}" {
                interfaces.push(current_interface.take().unwrap());
                continue;
            }

            if let Some(rest) = trimmed.strip_prefix("enum ") {
                let enum_name = rest.trim_end_matches('{').trim();
                current_enum = Some((kebab_to_pascal(enum_name), Vec::new()));
            } else if let Some(rest) = trimmed.strip_prefix("record ") {
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
                iface.functions.push(format!(
                    "  export function {}({}): {};",
                    kebab_to_camel(fn_name.trim()),
                    params.join(", "),
                    ret_type
                ));
            }
        } else if let Some(rest) = trimmed.strip_prefix("interface ")
            && let Some((iface_name, _)) = rest.split_once('{')
        {
            let name = iface_name.trim().to_string();
            // Dynamically include interfaces declared as imported in world
            if imported_interfaces.contains(&name) {
                current_interface = Some(WitInterface {
                    name,
                    functions: Vec::new(),
                    records: Vec::new(),
                    enums: Vec::new(),
                });
            }
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

    for (i, iface) in interfaces.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        let module_id = format!("{package_name}/{}{package_version}", iface.name);
        out.push_str(&format!("declare module '{module_id}' {{\n"));
        out.push_str(&format!("  /** @module Interface {module_id} **/\n"));
        for func in &iface.functions {
            out.push_str(func);
            out.push('\n');
        }
        for (enum_name, cases) in &iface.enums {
            let union_type = cases.iter().map(|c| format!("'{c}'")).collect::<Vec<_>>().join(" | ");
            out.push_str(&format!("  export type {enum_name} = {union_type};\n"));
        }
        for (rec_name, fields) in &iface.records {
            out.push_str(&format!("  export interface {rec_name} {{\n"));
            for (f_name, f_type) in fields {
                out.push_str(&format!("    {f_name}: {f_type};\n"));
            }
            out.push_str("  }\n");
        }
        out.push_str("}\n");
    }

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
