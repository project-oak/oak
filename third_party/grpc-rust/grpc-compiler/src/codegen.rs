use std::collections::HashMap;

use protobuf;
use protobuf::compiler_plugin;
use protobuf::descriptor::*;
use protobuf::descriptorx::*;
use protobuf::Message;
use protobuf_codegen::code_writer::CodeWriter;

/// Adjust method name to follow Rust style.
fn snake_name(name: &str) -> String {
    let mut snake_method_name = String::with_capacity(name.len());
    let mut chars = name.chars();
    // initial char can be any char except '_'.
    let mut last_char = '.';
    'outer: while let Some(c) = chars.next() {
        // Please note that '_' is neither uppercase nor lowercase.
        if !c.is_uppercase() {
            last_char = c;
            snake_method_name.push(c);
            continue;
        }
        let mut can_append_underscore = false;
        // check if it's the first char.
        if !snake_method_name.is_empty() && last_char != '_' {
            snake_method_name.push('_');
        }
        last_char = c;
        // find all continous upper case char and append an underscore before
        // last upper case char if neccessary.
        while let Some(c) = chars.next() {
            if !c.is_uppercase() {
                if can_append_underscore && c != '_' {
                    snake_method_name.push('_');
                }
                snake_method_name.extend(last_char.to_lowercase());
                snake_method_name.push(c);
                last_char = c;
                continue 'outer;
            }
            snake_method_name.extend(last_char.to_lowercase());
            last_char = c;
            can_append_underscore = true;
        }
        snake_method_name.extend(last_char.to_lowercase());
    }
    snake_method_name
}

struct MethodGen<'a> {
    proto: &'a MethodDescriptorProto,
    service_path: String,
    root_scope: &'a RootScope<'a>,
}

impl<'a> MethodGen<'a> {
    fn new(
        proto: &'a MethodDescriptorProto,
        service_path: String,
        root_scope: &'a RootScope<'a>,
    ) -> MethodGen<'a> {
        MethodGen {
            proto: proto,
            service_path: service_path,
            root_scope: root_scope,
        }
    }

    fn snake_name(&self) -> String {
        snake_name(self.proto.get_name())
    }

    fn input_empty(&self) -> bool {
        self.root_scope
            .find_message(self.proto.get_input_type())
            .message
            == protobuf::well_known_types::Empty::descriptor_static().get_proto()
    }

    fn output_empty(&self) -> bool {
        self.root_scope
            .find_message(self.proto.get_output_type())
            .message
            == protobuf::well_known_types::Empty::descriptor_static().get_proto()
    }

    fn input_message(&self) -> String {
        let msg = self.root_scope.find_message(self.proto.get_input_type());
        let empty = protobuf::well_known_types::Empty::descriptor_static();
        if msg.message == empty.get_proto() {
            "()".to_string()
        } else {
            format!("super::{}", msg.rust_fq_name())
        }
    }

    fn output_message(&self) -> String {
        let msg = self.root_scope.find_message(self.proto.get_output_type());
        let empty = protobuf::well_known_types::Empty::descriptor_static();
        if msg.message == empty.get_proto() {
            "()".to_string()
        } else {
            format!("super::{}", msg.rust_fq_name())
        }
    }

    fn server_req_type(&self) -> String {
        match self.proto.get_client_streaming() {
            false => format!("{}", self.input_message()),
            // TODO: better streaming
            true => format!("Vec<{}>", self.input_message()),
        }
    }

    fn server_resp_type(&self) -> String {
        match self.proto.get_server_streaming() {
            false => format!("{}", self.output_message()),
            // TODO: better streaming
            true => format!("Vec<{}>", self.output_message()),
        }
    }

    fn server_sig(&self) -> String {
        let arg;
        if self.input_empty() {
            arg = "".to_string();
        } else {
            arg = format!(
                ", {}: {}",
                if self.proto.get_client_streaming() {
                    "reqs"
                } else {
                    "req"
                },
                self.server_req_type(),
            );
        }
        let result;
        if self.output_empty() {
            result = "".to_string();
        } else {
            result = format!(" -> {}", self.server_resp_type());
        }
        format!("{}(&mut self{}){}", self.snake_name(), arg, result)
    }

    fn write_server_intf(&self, w: &mut CodeWriter) {
        w.fn_def(&self.server_sig())
    }

    fn streaming_upper(&self) -> &'static str {
        match (
            self.proto.get_client_streaming(),
            self.proto.get_server_streaming(),
        ) {
            (false, false) => "Unary",
            (false, true) => "ServerStreaming",
            (true, false) => "ClientStreaming",
            (true, true) => "Bidi",
        }
    }

    fn write_dispatch(&self, w: &mut CodeWriter) {
        // TODO: rather than explicitly generating dispatch() boilerplate, instead
        // invoke a generic method that accepts the relevant request/response types.
        let param_in;
        if self.input_empty() {
            param_in = "";
        } else {
            match self.proto.get_client_streaming() {
                false => {
                    param_in = "req";
                    w.write_line("let req = protobuf::parse_from_reader(grpc_channel).unwrap();")
                }
                true => {
                    param_in = "reqs";
                    w.write_line("let mut reqs = vec![];");
                    w.block("loop {", "}", |w| {
                        w.block(
                            "match protobuf::parse_from_reader(grpc_channel) {",
                            "}",
                            |w| {
                                w.write_line("Err(_) => break,");
                                w.write_line("Ok(req) => reqs.push(req),");
                            },
                        );
                    });
                }
            }
        }
        if self.output_empty() {
            w.write_line(&format!("node.{}({});", self.snake_name(), param_in));
        } else {
            match self.proto.get_server_streaming() {
                false => {
                    w.write_line(&format!(
                        "let rsp = node.{}({});",
                        self.snake_name(),
                        param_in
                    ));
                    w.write_line("rsp.write_to_writer(grpc_channel).unwrap();");
                }
                true => {
                    w.write_line(&format!(
                        "let rsps = node.{}({});",
                        self.snake_name(),
                        param_in
                    ));
                    w.block("for rsp in rsps {", "}", |w| {
                        w.write_line("rsp.write_to_writer(grpc_channel).unwrap();");
                    });
                }
            }
        }
    }

    fn write_descriptor(&self, w: &mut CodeWriter, before: &str, after: &str) {
        w.block(
            &format!("{}{}", before, "::grpc::rt::MethodDescriptor {"),
            &format!("{}{}", "}", after),
            |w| {
                w.field_entry(
                    "name",
                    &format!(
                        "::grpc::rt::StringOrStatic::Static(\"{}/{}\")",
                        self.service_path,
                        self.proto.get_name()
                    ),
                );
                w.field_entry(
                    "streaming",
                    &format!("::grpc::rt::GrpcStreaming::{}", self.streaming_upper()),
                );
                w.field_entry(
                    "req_marshaller",
                    "::grpc::rt::ArcOrStatic::Static(&::grpc_protobuf::MarshallerProtobuf)",
                );
                w.field_entry(
                    "resp_marshaller",
                    "::grpc::rt::ArcOrStatic::Static(&::grpc_protobuf::MarshallerProtobuf)",
                );
            },
        );
    }
}

struct ServiceGen<'a> {
    proto: &'a ServiceDescriptorProto,
    _root_scope: &'a RootScope<'a>,
    methods: Vec<MethodGen<'a>>,
    service_path: String,
    _package: String,
}

impl<'a> ServiceGen<'a> {
    fn new(
        proto: &'a ServiceDescriptorProto,
        file: &FileDescriptorProto,
        root_scope: &'a RootScope,
    ) -> ServiceGen<'a> {
        let service_path = if file.get_package().is_empty() {
            format!("/{}", proto.get_name())
        } else {
            format!("/{}.{}", file.get_package(), proto.get_name())
        };
        let methods = proto
            .get_method()
            .into_iter()
            .map(|m| MethodGen::new(m, service_path.clone(), root_scope))
            .collect();

        ServiceGen {
            proto,
            _root_scope: root_scope,
            methods,
            service_path,
            _package: file.get_package().to_string(),
        }
    }

    // server struct name
    fn server_name(&self) -> String {
        format!("{}Server", self.proto.get_name())
    }

    // trait name
    fn server_intf_name(&self) -> String {
        format!("{}Node", self.proto.get_name())
    }

    fn write_server_intf(&self, w: &mut CodeWriter) {
        w.pub_trait(&self.server_intf_name(), |w| {
            for (i, method) in self.methods.iter().enumerate() {
                if i != 0 {
                    w.write_line("");
                }

                method.write_server_intf(w);
            }
        });
    }

    fn write_service_definition(
        &self,
        before: &str,
        after: &str,
        handler: &str,
        w: &mut CodeWriter,
    ) {
        w.block(
            &format!("{}::grpc::rt::ServerServiceDefinition::new(\"{}\",",
                before, self.service_path),
            &format!("){}", after),
            |w| {
                w.block("vec![", "],", |w| {
                    for method in &self.methods {
                        w.block("::grpc::rt::ServerMethod::new(", "),", |w| {
                            method.write_descriptor(w, "::grpc::rt::ArcOrStatic::Static(&", "),");
                            w.block("{", "},", |w| {
                                w.write_line(&format!("let handler_copy = {}.clone();", handler));
                                w.write_line(&format!("::grpc::rt::MethodHandler{}::new(move |ctx, req, resp| (*handler_copy).{}(ctx, req, resp))",
                                    method.streaming_upper(),
                                    method.snake_name()));
                            });
                        });
                    }
                });
            });
    }

    fn write_server(&self, w: &mut CodeWriter) {
        w.write_line(&format!("pub struct {};", self.server_name()));

        w.write_line("");

        w.write_line("");

        w.impl_self_block(&self.server_name(), |w| {
            w.pub_fn(&format!("new_service_def<H : {} + 'static + Sync + Send + 'static>(handler: H) -> ::grpc::rt::ServerServiceDefinition", self.server_intf_name()), |w| {
                w.write_line("let handler_arc = ::std::sync::Arc::new(handler);");

                self.write_service_definition("", "", "handler_arc", w);
            });
        });
    }

    fn write_dispatcher(&self, w: &mut CodeWriter) {
        w.pub_fn(&format!("dispatch(node: &mut {}, grpc_method_name: &str, grpc_channel: &mut oak::Channel)", self.server_intf_name()), |w| {
            w.block("match grpc_method_name {", "};", |w| {
                for method in &self.methods {
                    let full_path = format!("{}/{}", method.service_path, method.proto.get_name());
                    w.block(&format!("\"{}\" => {{", full_path), "}", |w| {
                        method.write_dispatch(w);
                    });
                }
                w.block("_ => {", "}", |w| {
                    w.write_line("writeln!(oak::logging_channel(), \"unknown method name: {}\", grpc_method_name).unwrap();");
                    w.write_line("panic!(\"unknown method name\");");
                });
            });
        });
    }

    fn write(&self, w: &mut CodeWriter) {
        w.write_line("use protobuf::Message;");
        w.write_line("use std::io::Write;");
        w.write_line("");
        w.comment("Oak node server interface");
        self.write_server_intf(w);
        w.write_line("");
        w.comment("Oak node gRPC method dispatcher");
        self.write_dispatcher(w);
    }
}

fn gen_file(
    file: &FileDescriptorProto,
    root_scope: &RootScope,
) -> Option<compiler_plugin::GenResult> {
    if file.get_service().is_empty() {
        return None;
    }

    let base = protobuf::descriptorx::proto_path_to_rust_mod(file.get_name());

    let mut v = Vec::new();
    {
        let mut w = CodeWriter::new(&mut v);
        w.write_generated();
        w.write_line("");

        for service in file.get_service() {
            w.write_line("");
            ServiceGen::new(service, file, root_scope).write(&mut w);
        }
    }

    Some(compiler_plugin::GenResult {
        name: base + "_grpc.rs",
        content: v,
    })
}

pub fn gen(
    file_descriptors: &[FileDescriptorProto],
    files_to_generate: &[String],
) -> Vec<compiler_plugin::GenResult> {
    let files_map: HashMap<&str, &FileDescriptorProto> =
        file_descriptors.iter().map(|f| (f.get_name(), f)).collect();

    let root_scope = RootScope {
        file_descriptors: file_descriptors,
    };

    let mut results = Vec::new();

    for file_name in files_to_generate {
        let file = files_map[&file_name[..]];

        if file.get_service().is_empty() {
            continue;
        }

        results.extend(gen_file(file, &root_scope).into_iter());
    }

    results
}

pub fn protoc_gen_grpc_rust_main() {
    compiler_plugin::plugin_main(gen);
}

#[cfg(test)]
mod test {
    #[test]
    fn test_snake_name() {
        let cases = vec![
            ("AsyncRequest", "async_request"),
            ("asyncRequest", "async_request"),
            ("async_request", "async_request"),
            ("createID", "create_id"),
            ("CreateIDForReq", "create_id_for_req"),
            ("Create_ID_For_Req", "create_id_for_req"),
            ("ID", "id"),
            ("id", "id"),
        ];

        for (origin, exp) in cases {
            let res = super::snake_name(&origin);
            assert_eq!(res, exp);
        }
    }
}
