(function() {
    var implementors = Object.fromEntries([["oak_containers_agent",[["impl&lt;S, T&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;T&gt;&gt; for <a class=\"struct\" href=\"oak_containers_agent/metrics/struct.MonitoringService.html\" title=\"struct oak_containers_agent::metrics::MonitoringService\">MonitoringService</a>&lt;S&gt;<div class=\"where\">where\n    S: Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;T&gt;&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    &lt;S as Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;T&gt;&gt;&gt;::Future: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a>,\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div>"]]],["oak_grpc",[["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_grpc/oak/containers/launcher_server/struct.LauncherServer.html\" title=\"struct oak_grpc::oak::containers::launcher_server::LauncherServer\">LauncherServer</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"oak_grpc/oak/containers/launcher_server/trait.Launcher.html\" title=\"trait oak_grpc::oak::containers::launcher_server::Launcher\">Launcher</a>,\n    B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div>"],["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_grpc/oak/containers/orchestrator_server/struct.OrchestratorServer.html\" title=\"struct oak_grpc::oak::containers::orchestrator_server::OrchestratorServer\">OrchestratorServer</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"oak_grpc/oak/containers/orchestrator_server/trait.Orchestrator.html\" title=\"trait oak_grpc::oak::containers::orchestrator_server::Orchestrator\">Orchestrator</a>,\n    B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div>"],["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_grpc/oak/containers/v1/hostlib_key_provisioning_server/struct.HostlibKeyProvisioningServer.html\" title=\"struct oak_grpc::oak::containers::v1::hostlib_key_provisioning_server::HostlibKeyProvisioningServer\">HostlibKeyProvisioningServer</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"oak_grpc/oak/containers/v1/hostlib_key_provisioning_server/trait.HostlibKeyProvisioning.html\" title=\"trait oak_grpc::oak::containers::v1::hostlib_key_provisioning_server::HostlibKeyProvisioning\">HostlibKeyProvisioning</a>,\n    B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div>"],["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_grpc/oak/containers/v1/orchestrator_crypto_server/struct.OrchestratorCryptoServer.html\" title=\"struct oak_grpc::oak::containers::v1::orchestrator_crypto_server::OrchestratorCryptoServer\">OrchestratorCryptoServer</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"oak_grpc/oak/containers/v1/orchestrator_crypto_server/trait.OrchestratorCrypto.html\" title=\"trait oak_grpc::oak::containers::v1::orchestrator_crypto_server::OrchestratorCrypto\">OrchestratorCrypto</a>,\n    B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div>"],["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_grpc/oak/debug/debug_service_server/struct.DebugServiceServer.html\" title=\"struct oak_grpc::oak::debug::debug_service_server::DebugServiceServer\">DebugServiceServer</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"oak_grpc/oak/debug/debug_service_server/trait.DebugService.html\" title=\"trait oak_grpc::oak::debug::debug_service_server::DebugService\">DebugService</a>,\n    B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div>"],["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_grpc/oak/functions/oak_functions_server/struct.OakFunctionsServer.html\" title=\"struct oak_grpc::oak::functions::oak_functions_server::OakFunctionsServer\">OakFunctionsServer</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"oak_grpc/oak/functions/oak_functions_server/trait.OakFunctions.html\" title=\"trait oak_grpc::oak::functions::oak_functions_server::OakFunctions\">OakFunctions</a>,\n    B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div>"],["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_grpc/oak/key_provisioning/v1/key_provisioning_server/struct.KeyProvisioningServer.html\" title=\"struct oak_grpc::oak::key_provisioning::v1::key_provisioning_server::KeyProvisioningServer\">KeyProvisioningServer</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"oak_grpc/oak/key_provisioning/v1/key_provisioning_server/trait.KeyProvisioning.html\" title=\"trait oak_grpc::oak::key_provisioning::v1::key_provisioning_server::KeyProvisioning\">KeyProvisioning</a>,\n    B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div>"],["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_grpc/oak/session/v1/streaming_session_server/struct.StreamingSessionServer.html\" title=\"struct oak_grpc::oak::session::v1::streaming_session_server::StreamingSessionServer\">StreamingSessionServer</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"oak_grpc/oak/session/v1/streaming_session_server/trait.StreamingSession.html\" title=\"trait oak_grpc::oak::session::v1::streaming_session_server::StreamingSession\">StreamingSession</a>,\n    B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div>"]]],["oak_hello_world_proto",[["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_hello_world_proto/oak/containers/example/trusted_application_server/struct.TrustedApplicationServer.html\" title=\"struct oak_hello_world_proto::oak::containers::example::trusted_application_server::TrustedApplicationServer\">TrustedApplicationServer</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"oak_hello_world_proto/oak/containers/example/trusted_application_server/trait.TrustedApplication.html\" title=\"trait oak_hello_world_proto::oak::containers::example::trusted_application_server::TrustedApplication\">TrustedApplication</a>,\n    B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div>"],["impl&lt;T, B&gt; Service&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.2.11/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;B&gt;&gt; for <a class=\"struct\" href=\"oak_hello_world_proto/oak/containers/example/untrusted_application_server/struct.UntrustedApplicationServer.html\" title=\"struct oak_hello_world_proto::oak::containers::example::untrusted_application_server::UntrustedApplicationServer\">UntrustedApplicationServer</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"oak_hello_world_proto/oak/containers/example/untrusted_application_server/trait.UntrustedApplication.html\" title=\"trait oak_hello_world_proto::oak::containers::example::untrusted_application_server::UntrustedApplication\">UntrustedApplication</a>,\n    B: <a class=\"trait\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html\" title=\"trait http_body::Body\">Body</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,\n    B::<a class=\"associatedtype\" href=\"https://docs.rs/http-body/0.4.6/http_body/trait.Body.html#associatedtype.Error\" title=\"type http_body::Body::Error\">Error</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.Into.html\" title=\"trait core::convert::Into\">Into</a>&lt;StdError&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + 'static,</div>"]]]]);
    if (window.register_implementors) {
        window.register_implementors(implementors);
    } else {
        window.pending_implementors = implementors;
    }
})()
//{"start":57,"fragment_lengths":[1373,11445,3140]}