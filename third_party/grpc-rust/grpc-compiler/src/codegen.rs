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
        #[allow(clippy::while_let_on_iterator)]
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
            proto,
            service_path,
            root_scope,
        }
    }

    fn snake_name(&self) -> String {
        snake_name(self.proto.get_name())
    }

    fn input_message(&self) -> String {
        let msg = self.root_scope.find_message(self.proto.get_input_type());
        let empty = protobuf::well_known_types::Empty::descriptor_static();
        if msg.message == empty.get_proto() {
            "protobuf::well_known_types::Empty".to_string()
        } else {
            format!("super::{}", msg.rust_fq_name())
        }
    }

    fn output_message(&self) -> String {
        let msg = self.root_scope.find_message(self.proto.get_output_type());
        let empty = protobuf::well_known_types::Empty::descriptor_static();
        if msg.message == empty.get_proto() {
            "protobuf::well_known_types::Empty".to_string()
        } else {
            format!("super::{}", msg.rust_fq_name())
        }
    }

    fn server_req_type(&self) -> String {
        if self.proto.get_client_streaming() {
            // TODO(#97): better client-side streaming
            format!("Vec<{}>", self.input_message())
        } else {
            self.input_message().to_string()
        }
    }

    fn server_resp_type(&self) -> String {
        if self.proto.get_server_streaming() {
            "".to_string()
        } else {
            format!(" -> grpc::Result<{}>", self.output_message())
        }
    }

    fn server_sig(&self) -> String {
        let arg = format!(
            ", {}: {}",
            if self.proto.get_client_streaming() {
                "reqs"
            } else {
                "req"
            },
            self.server_req_type(),
        );
        let arg2 = if self.proto.get_server_streaming() {
            ", writer: grpc::ChannelResponseWriter".to_string()
        } else {
            "".to_string()
        };
        format!(
            "{}(&mut self{}{}){}",
            self.snake_name(),
            arg,
            arg2,
            self.server_resp_type()
        )
    }

    fn write_server_intf(&self, w: &mut CodeWriter) {
        w.fn_def(&self.server_sig())
    }

    fn full_path(&self) -> String {
        format!("{}/{}", self.service_path, self.proto.get_name())
    }

    fn client_resp_type(&self) -> String {
        format!(
            " -> grpc::Result<{}>",
            if self.proto.get_server_streaming() {
                // TODO(#592): ideally the return type for a streaming method would be
                //   format!("oak::io::Receiver<{}>", self.output_message());
                // This is not possible with the current io::Receiver's direct use of
                // the underlying handle.
                "oak::io::Receiver<grpc::GrpcResponse>".to_string()
            } else {
                self.output_message()
            }
        )
    }

    fn client_sig(&self) -> Option<String> {
        if self.proto.get_client_streaming() {
            // TODO(#97): support client-side streaming
            return None;
        }
        Some(format!(
            "{}(&self, req: {}){}",
            self.snake_name(),
            self.server_req_type(),
            self.client_resp_type()
        ))
    }

    fn write_client_impl(&self, w: &mut CodeWriter) {
        if let Some(sig) = self.client_sig() {
            w.pub_fn(&sig, |w| {
                w.write_line(format!(
                    "oak::grpc::{}(\"{}\", req, &self.0.invocation_sender)",
                    if self.proto.get_server_streaming() {
                        "invoke_grpc_method_stream"
                    } else {
                        "invoke_grpc_method"
                    },
                    self.full_path()
                ));
            });
        }
    }

    fn dispatch_method(&self) -> String {
        // Figure out which generic function applies
        let (gen_fn, lambda_params) = if self.proto.get_client_streaming() {
            if self.proto.get_server_streaming() {
                ("grpc::handle_stream_stream", "rr, w")
            } else {
                ("grpc::handle_stream_rsp", "rr")
            }
        } else if self.proto.get_server_streaming() {
            ("grpc::handle_req_stream", "r, w")
        } else {
            ("grpc::handle_req_rsp", "r")
        };
        format!(
            "{}(|{}| node.{}({}), req, writer)",
            gen_fn,
            lambda_params,
            self.snake_name(),
            lambda_params
        )
    }
}

struct ServiceGen<'a> {
    proto: &'a ServiceDescriptorProto,
    _root_scope: &'a RootScope<'a>,
    methods: Vec<MethodGen<'a>>,
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
            .iter()
            .map(|m| MethodGen::new(m, service_path.clone(), root_scope))
            .collect();

        ServiceGen {
            proto,
            _root_scope: root_scope,
            methods,
            _package: file.get_package().to_string(),
        }
    }

    // trait name for server functionality
    fn server_intf_name(&self) -> String {
        // Just use the service name, unadorned.
        self.proto.get_name().to_string()
    }

    fn write_server_intf(&self, w: &mut CodeWriter) {
        w.pub_trait(&self.server_intf_name(), |w| {
            for method in &self.methods {
                method.write_server_intf(w);
            }
        });
    }

    fn write_dispatcher(&self, w: &mut CodeWriter) {
        w.pub_fn(&format!("dispatch<T: {}>(node: &mut T, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter)", self.server_intf_name()), |w| {
            w.block("match method {", "};", |w| {
                for method in &self.methods {
                    w.write_line(format!("\"{}\" => {},", method.full_path(), method.dispatch_method()));
                }
                w.block("_ => {", "}", |w| {
                    w.write_line("panic!(\"unknown method name: {}\", method);");
                });
            });
        });
    }

    // trait name for client functionality
    fn client_intf_name(&self) -> String {
        format!("{}Client", self.proto.get_name())
    }

    fn write_client(&self, w: &mut CodeWriter) {
        w.write_line(format!(
            "pub struct {}(pub oak::grpc::client::Client);",
            self.client_intf_name(),
        ));
        w.write_line("");
        w.impl_self_block(self.client_intf_name(), |w| {
            for method in &self.methods {
                method.write_client_impl(w);
            }
        });
    }

    fn write(&self, w: &mut CodeWriter) {
        w.write_line("use oak::grpc;");
        w.write_line("use protobuf::Message;");
        w.write_line("use std::io::Write;");
        w.write_line("");
        w.comment("Oak Node server interface");
        self.write_server_intf(w);
        w.write_line("");
        w.comment("Oak Node gRPC method dispatcher");
        self.write_dispatcher(w);
        w.write_line("");
        w.comment("Client interface");
        self.write_client(w);
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
    let root_scope = RootScope { file_descriptors };
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
