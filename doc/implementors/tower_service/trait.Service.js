(function() {var implementors = {
"oak_functions_launcher":[["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.8/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_functions_launcher/server/proto/unary_session_server/struct.UnarySessionServer.html\" title=\"struct oak_functions_launcher::server::proto::unary_session_server::UnarySessionServer\">UnarySessionServer</a>&lt;T&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: <a class=\"trait\" href=\"oak_functions_launcher/server/proto/unary_session_server/trait.UnarySession.html\" title=\"trait oak_functions_launcher::server::proto::unary_session_server::UnarySession\">UnarySession</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.5/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,<br>&nbsp;&nbsp;&nbsp;&nbsp;B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.5/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;<a class=\"type\" href=\"https://docs.rs/tonic/0.8.2/tonic/codegen/type.StdError.html\" title=\"type tonic::codegen::StdError\">StdError</a>&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</span>"]],
"oak_grpc_unary_attestation":[["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.8/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_grpc_unary_attestation/proto/unary_session_server/struct.UnarySessionServer.html\" title=\"struct oak_grpc_unary_attestation::proto::unary_session_server::UnarySessionServer\">UnarySessionServer</a>&lt;T&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: <a class=\"trait\" href=\"oak_grpc_unary_attestation/proto/unary_session_server/trait.UnarySession.html\" title=\"trait oak_grpc_unary_attestation::proto::unary_session_server::UnarySession\">UnarySession</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.5/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,<br>&nbsp;&nbsp;&nbsp;&nbsp;B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.5/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</span>"]],
"trusted_shuffler_backend":[["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.8/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"trusted_shuffler_backend/echo/echo_server/struct.EchoServer.html\" title=\"struct trusted_shuffler_backend::echo::echo_server::EchoServer\">EchoServer</a>&lt;T&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: <a class=\"trait\" href=\"trusted_shuffler_backend/echo/echo_server/trait.Echo.html\" title=\"trait trusted_shuffler_backend::echo::echo_server::Echo\">Echo</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.5/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,<br>&nbsp;&nbsp;&nbsp;&nbsp;B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.5/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;<a class=\"type\" href=\"https://docs.rs/tonic/0.7.2/tonic/codegen/type.StdError.html\" title=\"type tonic::codegen::StdError\">StdError</a>&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</span>"]],
"trusted_shuffler_common":[["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.8/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"trusted_shuffler_common/echo/echo_server/struct.EchoServer.html\" title=\"struct trusted_shuffler_common::echo::echo_server::EchoServer\">EchoServer</a>&lt;T&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: <a class=\"trait\" href=\"trusted_shuffler_common/echo/echo_server/trait.Echo.html\" title=\"trait trusted_shuffler_common::echo::echo_server::Echo\">Echo</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.5/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,<br>&nbsp;&nbsp;&nbsp;&nbsp;B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.5/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</span>"]],
"trusted_shuffler_server":[["impl Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.8/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;Body&gt;&gt; for <a class=\"struct\" href=\"trusted_shuffler_server/http/struct.Service.html\" title=\"struct trusted_shuffler_server::http::Service\">Service</a>"],["impl&lt;T&gt; Service&lt;T&gt; for <a class=\"struct\" href=\"trusted_shuffler_server/http/struct.ServiceBuilder.html\" title=\"struct trusted_shuffler_server::http::ServiceBuilder\">ServiceBuilder</a>"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()