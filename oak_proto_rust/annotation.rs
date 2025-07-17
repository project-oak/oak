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

use std::{collections::HashSet, fs::File, io::Read, path::PathBuf};

use prost::Message;
use prost_types::FileDescriptorSet;

#[derive(Default)]
pub struct AnnotationInfo {
    pub annotate_types: HashSet<String>,
    pub oneof_fields: HashSet<String>,
    pub bytes_fields: HashSet<String>,
    pub optional_bytes_fields: HashSet<String>,
    pub repeated_bytes_fields: HashSet<String>,
}

impl AnnotationInfo {
    /// Collects annotation information for protobuf messages.
    ///
    /// This function compiles the given protobuf files and iterates through the
    /// message definitions to collect information required for generating
    /// serde annotations.
    ///
    /// # Arguments
    ///
    /// * `proto_paths` - A slice of paths to the `.proto` files to be compiled.
    /// * `included_protos` - A vector of include paths for the protobuf
    ///   compiler.
    /// * `package_prefix` - A string slice specifying the package prefix to
    ///   filter which messages to process (e.g., "oak").
    /// * `needed_types` - An optional `HashSet` of fully qualified message
    ///   names to process. If `Some`, only messages in this set will be
    ///   processed. If `None`, all messages matching the `package_prefix` will
    ///   be processed.
    pub fn collect_annotations(
        proto_paths: &[&str],
        included_protos: &[PathBuf],
        package_prefix: &str,
        needed_types: Option<&HashSet<String>>,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let descriptor_set = get_file_descriptor_set(proto_paths, included_protos)?;
        let mut annotations = AnnotationInfo::default();

        // Iterate over each .proto file
        for file_descriptor in descriptor_set
            .file
            .iter()
            .filter(|ds| ds.package.clone().unwrap_or_default().starts_with(package_prefix))
        {
            let package = &file_descriptor.package.clone().unwrap();

            // Iterate over each message type in the file
            for message_descriptor in &file_descriptor.message_type {
                if let Some(needed_types) = needed_types {
                    let full_qualified_message_name =
                        format!("{}.{}", package, message_descriptor.name());
                    if !needed_types.contains(&full_qualified_message_name) {
                        continue;
                    }
                }
                process_message(message_descriptor, package, &mut annotations);
            }
        }
        Ok(annotations)
    }

    /// Applies serde annotations to the given protobuf messages so that it can
    /// be serialized and deserialized in a json-proto compatible way.
    pub fn apply(&self, config: &mut prost_build::Config) {
        for message_type in self.annotate_types.iter().chain(self.oneof_fields.iter()) {
            config.type_attribute(message_type, "#[derive(serde::Serialize, serde::Deserialize)]");
            config.type_attribute(message_type, "#[serde(rename_all = \"camelCase\")]");
        }

        for message_type in &self.annotate_types {
            config.type_attribute(message_type, "#[serde(default)]");
        }

        for message_type in &self.oneof_fields {
            config.field_attribute(message_type, "#[serde(flatten)]");
        }

        for bytes_field in &self.bytes_fields {
            config.field_attribute(bytes_field, "#[serde(with=\"crate::base64data\")]");
        }

        for bytes_field in &self.optional_bytes_fields {
            config
                .field_attribute(bytes_field, "#[serde(with=\"crate::base64data::option_bytes\")]");
        }

        for bytes_field in &self.repeated_bytes_fields {
            config.field_attribute(
                bytes_field,
                "#[serde(with=\"crate::base64data::repeated_bytes\")]",
            );
        }
    }
}

fn get_file_descriptor_set(
    proto_paths: &[&str],
    included_protos: &[PathBuf],
) -> Result<FileDescriptorSet, Box<dyn std::error::Error>> {
    let out_dir = PathBuf::from(std::env::var("OUT_DIR")?);
    let descriptor_path = out_dir.join("file_descriptor_set.bin");
    prost_build::Config::new()
        .file_descriptor_set_path(&descriptor_path)
        .compile_protos(proto_paths, included_protos)?;

    let mut file = File::open(&descriptor_path)?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf)?;
    std::fs::remove_file(&descriptor_path)?;

    Ok(FileDescriptorSet::decode(buf.as_slice())?)
}

fn process_message(
    message_descriptor: &prost_types::DescriptorProto,
    package: &str,
    annotations: &mut AnnotationInfo,
) {
    let message_name = message_descriptor.name();
    let qualified_message_name = format!("{}.{}", package, message_name);

    annotations.annotate_types.insert(qualified_message_name.clone());
    // Iterate over each field in the message
    for field_descriptor in message_descriptor.field.iter().filter(|fd| fd.oneof_index.is_none()) {
        if field_descriptor.r#type() == prost_types::field_descriptor_proto::Type::Bytes {
            let field_name = field_descriptor.name();
            let qualified_field_name = format!("{}.{}", qualified_message_name, field_name);
            match field_descriptor.label() {
                prost_types::field_descriptor_proto::Label::Repeated => {
                    annotations.repeated_bytes_fields.insert(qualified_field_name);
                }
                _ => {
                    if field_descriptor.proto3_optional() {
                        annotations.optional_bytes_fields.insert(qualified_field_name);
                    } else {
                        annotations.bytes_fields.insert(qualified_field_name);
                    }
                }
            }
        }
    }
    for oneof_descriptor in &message_descriptor.oneof_decl {
        let oneof_name = oneof_descriptor.name();
        let qualified_oneof_name = format!("{}.{}", qualified_message_name, oneof_name);
        annotations.oneof_fields.insert(qualified_oneof_name);
    }
}
