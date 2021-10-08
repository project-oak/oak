# Programming Oak

This document walks through the basics of programming in Oak.

- [Writing an Oak Node](#writing-an-oak-node)
  - [Per-Node Boilerplate](#per-node-boilerplate)
  - [Generated gRPC service code](#generated-grpc-service-code)
- [Running an Oak Application](#running-an-oak-application)
  - [Creating a Configuration File](#creating-a-configuration-file)
  - [Starting the Oak Application](#starting-the-oak-application)
  - [Configuring the Oak Application](#configuring-the-oak-application)
- [Using an Oak Application from a client](#using-an-oak-application-from-a-client)
- [gRPC Request Processing Path](#grpc-request-processing-path)
- [Nodes, Channels and Handles](#nodes-channels-and-handles)
- [Persistent Storage](#persistent-storage)
- [Using External gRPC Services](#using-external-grpc-services)
- [Testing](#testing)
  - [Testing Multi-Node Applications](#testing-multi-node-applications)

## Writing an Oak Node

Oak Applications are built from a collection of inter-connected Oak **Nodes**,
so the first step is to understand how to build a single Oak Node.

Writing software for the Oak system involves a certain amount of boilerplate, so
this section will cover the hows &ndash; and whys &ndash; of this, using code
taken from the various [examples](../examples/). If you're impatient, you could
start by copying the `hello_world` example in particular, and just try modifying
things from there.

### Per-Node Boilerplate

An Oak Node needs to provide a single [entrypoint](abi.md#exported-function),
which is the point at which Node execution begins. However, Node authors don't
_have_ to implement this function themselves; for a Node which receives messages
(a combination of bytes and handles) that can be
[decoded](https://project-oak.github.io/oak/sdk/doc/oak/io/trait.Decodable.html)
into a Rust type, there are helper functions in the Oak SDK that make this
easier, and are the idiomatic and recommended way of implementing Applications.

To use these helpers, an Oak Node should be a `struct` of some kind to represent
the internal state of the Node itself (which may be empty), implement the
[`oak::CommandHandler`](https://project-oak.github.io/oak/sdk/doc/oak/trait.CommandHandler.html)
trait for it, then define an
[`entrypoint_command_handler!`](https://project-oak.github.io/oak/sdk/doc/oak/macro.entrypoint_command_handler.html)
so the Oak SDK knows how to instantiate it.

The
[`entrypoint_command_handler!`](https://project-oak.github.io/oak/sdk/doc/oak/macro.entrypoint_command_handler.html)
macro defines the exported function using the lower-level
[`entrypoint!`](https://project-oak.github.io/oak/sdk/doc/oak/macro.entrypoint.html)
macro (which requires a function to run as the Node entrypoint).

Under the covers the
[`entrypoint!`](https://project-oak.github.io/oak/sdk/doc/oak/macro.entrypoint.html)
macro converts the provided function body into an
[external function](abi.md#exported-function) suitable for WebAssembly use,
[taking care](#panic-handling) of
[handling `panic`s](https://doc.rust-lang.org/nomicon/ffi.html#ffi-and-panics).

For an Oak Application that exposes itself as a gRPC server (the normal "front
door" for an Oak Application), the easiest way to set things up is to define two
nodes:

- a main Node
- a gRPC service handler Node

We will describe them in the next sections, starting with the gRPC service
handler Node.

#### gRPC Service Handler Node

This Node implements the logic related to handling
[`GrpcInvocation`](https://project-oak.github.io/oak/sdk/doc/oak/proto/oak/invocation/struct.GrpcInvocation.html)
messages coming from a gRPC server pseudo-Node.

In order to implement it:

- define a `struct` holding the internal state of the gRPC service, or just an
  empty `struct` if no state is needed.
- implement the auto-generated gRPC service trait for the Node handler `struct`.
- define an
  [`impl_dispatcher!`](https://project-oak.github.io/oak/sdk/doc/oak/macro.impl_dispatcher.html)
  entry, specifying the appropriate auto-generated gRPC dispatcher, in order to
  automatically make the handler `struct` implement the
  [`CommandHandler`](https://project-oak.github.io/oak/sdk/doc/oak/trait.CommandHandler.html)
  trait.

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/translator/module/rust/src/lib.rs Rust /oak::entrypoint_command_handler_init!\(handler/ /^}/)
```Rust
oak::entrypoint_command_handler_init!(handler => Handler);
oak::impl_dispatcher!(impl Handler : TranslatorDispatcher);

#[derive(Default)]
struct Handler;

impl Translator for Handler {
    fn translate(&mut self, req: TranslateRequest) -> grpc::Result<TranslateResponse> {
        info!(
            "Attempt to translate '{}' from {} to {}",
            req.text, req.from_lang, req.to_lang
        );
        let rsp = TranslateResponse {
            translated_text: match req.from_lang.as_str() {
                "en" => match req.text.as_str() {
                    "WORLDS" => match req.to_lang.as_str() {
                        "fr" => "MONDES".to_string(),
                        "it" => "MONDI".to_string(),
                        _ => {
                            info!("Output language {} not found", req.to_lang);
                            return Err(grpc::build_status(
                                grpc::Code::NotFound,
                                "Output language not found",
                            ));
                        }
                    },
                    _ => {
                        info!(
                            "Input text '{}' in {} not recognized",
                            req.text, req.from_lang
                        );
                        return Err(grpc::build_status(
                            grpc::Code::NotFound,
                            "Input text unrecognized",
                        ));
                    }
                },
                _ => {
                    info!("Input language '{}' not recognized", req.from_lang);
                    return Err(grpc::build_status(
                        grpc::Code::NotFound,
                        "Input language unrecognized",
                    ));
                }
            },
        };
        info!("Translation '{}'", rsp.translated_text);
        Ok(rsp)
    }
}
```
<!-- prettier-ignore-end -->

#### Main Node

It is common for an Oak Application to define a "main" Node which is the overall
entrypoint of the Application, and it is in charge of creating all the other
Nodes and Channels that are going to be used by the Application. This Node is
also modelled as a
[`oak::CommandHandler`](https://project-oak.github.io/oak/sdk/doc/oak/trait.CommandHandler.html)
whose command type is
[`ConfigMap`](https://project-oak.github.io/oak/sdk/doc/oak/proto/oak/application/struct.ConfigMap.html),
even though in practice it is expected to receive a single
[`ConfigMap`](https://project-oak.github.io/oak/sdk/doc/oak/proto/oak/application/struct.ConfigMap.html)
instance, so the "loop" is only really executed exactly once.

- from the body of the main Node of the Application, create an instance of the
  handler Node via
  [`entrypoint_node_create`](https://project-oak.github.io/oak/sdk/doc/oak/io/fn.entrypoint_node_create.html)
  (or by manually calling
  [`node_create`](https://project-oak.github.io/oak/sdk/doc/oak/io/fn.node_create.html)),
  which returns a
  [`Sender`](https://project-oak.github.io/oak/sdk/doc/oak/io/struct.Sender.html)
  of
  [`GrpcInvocation`](https://project-oak.github.io/oak/sdk/doc/oak/proto/oak/invocation/struct.GrpcInvocation.html)
  messages to send to the handler Node.
- call the
  [`oak::grpc::server::init_with_sender`](https://project-oak.github.io/oak/sdk/doc/oak/grpc/server/fn.init_with_sender.html)
  helper by passing the newly created
  [`Sender`](https://project-oak.github.io/oak/sdk/doc/oak/io/struct.Sender.html)
  to it; this creates a new gRPC server pseudo-Node that sends gRPC invocations
  to the provided
  [`Sender`](https://project-oak.github.io/oak/sdk/doc/oak/io/struct.Sender.html),
  which in this case is connected directly to the gRPC server handler Node that
  we have previously defined.

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/translator/module/rust/src/lib.rs Rust /oak::entrypoint_command_handler!\(oak_main/ /^}/)
```Rust
oak::entrypoint_command_handler!(oak_main => Main);

#[derive(Default)]
struct Main;

impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, _command: ConfigMap) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        let router_sender = oak::io::entrypoint_node_create::<Router, _, _>(
            "router",
            &Label::public_untrusted(),
            "app",
            LogInit {
                log_sender: Some(log_sender),
            },
        )
        .context("Couldn't create router node")?;
        oak::grpc::server::init_with_sender("[::]:8080", router_sender)
            .context("Couldn't create gRPC server pseudo-Node")?;
        Ok(())
    }
}
```
<!-- prettier-ignore-end -->

#### Panic Handling

Any Rust panic originating in an Oak Node must be caught before going through
the Wasm FFI boundary. If you use the `entrypoint!` macro, this is done for you,
but a manually implemented Node should use the
[`catch_unwind`](https://doc.rust-lang.org/std/panic/fn.catch_unwind.html)
method from the Rust standard library:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/abitest/module_0/rust/src/lib.rs Rust /^#.*no_mangle.*/ /^}/)
```Rust
#[no_mangle]
pub extern "C" fn frontend_oak_main(_in_handle: u64) {
    let _ = std::panic::catch_unwind(|| {
        oak::set_panic_hook();
        let node = FrontendNode::new();
        let grpc_channel =
            oak::grpc::server::init("[::]:8080").expect("could not create gRPC server pseudo-Node");
        oak::run_command_loop(node, grpc_channel.iter());
    });
}
```
<!-- prettier-ignore-end -->

### Generated gRPC service code

The Oak SDK provides
[`oak_utils::compile_protos`](https://project-oak.github.io/oak/oak_utils/doc/oak_utils/fn.compile_protos.html)
to autogenerate Rust code from a
[gRPC service definition](https://grpc.io/docs/guides/concepts/). Adding a
`build.rs` file to the Node that uses this function results in a generated file
`<service>_grpc.rs` appearing under the crate's build
[`OUT_DIR`](https://doc.rust-lang.org/cargo/reference/environment-variables.html)
(by default).

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/translator/common/build.rs Rust /fn main/ /^}/)
```Rust
fn main() {
    // Generate the Oak-specific server and client code for the gRPC service,
    // along with the Rust types corresponding to the message definitions.
    oak_utils::compile_protos(&["examples/translator/proto/translator.proto"], "../../..");
}
```
<!-- prettier-ignore-end -->

The autogenerated code includes three parts, described in more detail below:

- A server-side trait definition.
- A `Dispatcher` `struct` that handles routing of server-side gRPC method
  invocations.
- A client-side `struct` to allow easy use of the gRPC service from an Oak Node.

The first part is a trait definition that includes a method for each of the
methods in the gRPC service, taking the relevant (auto-generated) request and
response types. The Oak Node handler struct implements the gRPC service by
implementing this trait [as described previously](#grpc-service-handler-node).

```Rust
pub trait Translator {
    fn translate(&mut self, req: TranslateRequest) -> ::oak::grpc::Result<TranslateResponse>;
}
```

The second part of the autogenerated code includes a `Dispatcher` struct which
maps a request method name to a pointer to the relevant method on the service
trait. This `Dispatcher` struct can then be used with the
[`impl_dispatcher!`](https://project-oak.github.io/oak/sdk/doc/oak/macro.impl_dispatcher.html)
macro to generate the entire implementation of the
[`ServerNode::invoke`](https://project-oak.github.io/oak/sdk/doc/oak/grpc/trait.ServerNode.html#tymethod.invoke)
method, and then in turn of
[`CommandHandler::handle_command`](https://project-oak.github.io/oak/sdk/doc/oak/trait.CommandHandler.html#tymethod.handle_command).

Taken altogether, these two parts cover all of the boilerplate needed to have a
Node act as a gRPC server:

- The "main" Node creates the handler Node implementation and the gRPC server
  pseudo-Node, connecting them together
- The handler Node struct implements the methods defined on the service trait,
  and delegates to the auto-generated `Dispatcher` via the `impl_dispatcher!`
  macro.

Finally, the third part of the autogenerated code includes a stub implementation
of the client side for the gRPC service. If a Node offers a gRPC service to
other Nodes in the same Application, they can use this client stub code to get
simple access to the service.

## Running an Oak Application

In order to run the Oak Application, each of the WebAssembly Nodes that comprise
the Application must first be compiled into one or more WebAssembly modules, and
these compiled WebAssembly modules are then assembled into an overall
Application Configuration File.

Each of these steps is described in the following sections.

### Compiling to Wasm Module

In order to build a WebAssembly module for an Oak WebAssembly Node, written in
Rust, `cargo build` should be used with `--target=wasm32-unknown-unknown`, as
follows:

```bash
cargo -Zunstable-options build --release \
  --target=wasm32-unknown-unknown \
  --manifest-path=examples/hello_world/module/rust/Cargo.toml \
  --out-dir=examples/hello_world/bin
```

The `--out-dir` option ensures that the resulting binary is copied into a
specific directory to allow later steps to find it. Since `--out-dir` is
unstable, `-Zunstable-options` is required as well.

### Creating a Configuration File

In order to load an Oak Application into the Oak Server its configuration must
be serialized into a binary file that will be parsed by the
[_Oak Application Builder_](../sdk/rust/oak_app_build), as follows:

```bash
cargo run --manifest-path=sdk/rust/oak_app_build/Cargo.toml -- \
  --manifest-path=examples/hello_world/oak_app_manifest.toml
```

The input file is the .toml manifest file and the output is the binary
containing all the needed modules, which will be generated under the `bin`
directory alongside the manifest file. Here is an example of a manifest file:

```toml
name = "hello_world"

[modules]
app = { path = "examples/hello_world/bin/hello_world.wasm" }
translator = { path = "examples/hello_world/bin/translator.wasm" }

```

All these steps are implemented as a part of the
`./scripts/runner run-examples --example-name=hello_world` script.

The Oak Application Builder also allows Wasm modules to be downloaded from an
external URL, such as [Google Cloud Storage](https://cloud.google.com/storage).
In order to do this, the application configuration file should include
`external` as a module location:

```toml
name = "hello_world"

[modules]
app = { external = { url = "https://storage.googleapis.com/oak-modules/hello_world/57ba0bcebf2c01389d0413736b0a3bb261312bcf0d6e87181359e402df751d50", sha256 = "57ba0bcebf2c01389d0413736b0a3bb261312bcf0d6e87181359e402df751d50" } }
translator = { path = "examples/hello_world/bin/translator.wasm" }

```

It is also possible to upload compiled Wasm modules to Google Cloud Storage
using the following script:

```bash
./scripts/push_example -e hello_world
```

### Creating a Permissions File

A permissions file is a `.toml` file provided by the host owner, as an
additional layer of defense. This file specifies the features of Oak that are
permitted for the applications running on the host. In particular, using this
file, the host owner can enable or disable gRPC or HTTP connections. In
addition, it is possible to specify an allowlist of external gRPC or HTTP
authorities (in the `[userinfo@]host[:port]` format) that the applications can
connect to over TLS. Interaction with all other authorities is prohibited.
Connections to insecure HTTP servers are allowed only if explicitly enabled via
the `allow_insecure_http_egress` flag.

Here is an example of a permissions file:

```toml
allow_grpc_server_nodes = true
allow_http_server_nodes = true
allow_log_nodes = true
allow_insecure_http_egress = true
allow_egress_https_authorities = ["localhost:8080", "localhost:8888"]

```

All permissions are denied by default. So, an empty permissions file is the most
restrictive one.

### Starting the Oak Application

The Oak Application is then started using the Oak Loader:

```bash
./oak_loader/target/x86_64-unknown-linux-musl/release/oak_loader \
  --application=./examples/hello_world/bin/hello_world.oak \
  --permissions=./examples/permissions/permissions.toml
```

Providing a permissions file via the `permissions` flag is only needed for the
Base (log-less) server releases.

The Oak Loader will launch an [Oak Runtime](concepts.md#oak-runtime), and this
Runtime will check the provided Wasm module(s) and application configuration.
Assuming everything is correct (e.g. the Nodes all have a main entrypoint and
only expect to link to the Oak [host functions](abi.md#host-functions)), the Oak
Runtime opens up the gRPC port specified by the Application Configuration, if
creating a gRPC connection is permitted in the permissions file. This port is
then used by clients to connect to the Oak Application.

### Configuring the Oak Application

The Application configuration [described above](#creating-a-configuration-file)
gives the configuration of the Application as seen by the Runtime: what Wasm
modules to load, what entrypoint to invoke. However, the Application may need
some start-of-day configuration of its own, roughly equivalent to runtime
options for a normal executable.

Oak supports this using a [`ConfigMap`](/oak_abi/proto/application.proto)
message, holding arbitrary key:value data for initial configuration. At
Application start-up, the Oak Runtime sends the serialized form of this message
as a single message on the initial Node's initial channel (and then closes the
channel).

The initial Node of an Application can retrieve this configuration by reading
from the implicit incoming channel, usually by implementing the
[`CommandHandler`](https://project-oak.github.io/oak/sdk/doc/oak/trait.CommandHandler.html)
trait setting the
[`Command`](https://project-oak.github.io/oak/sdk/doc/oak/trait.CommandHandler.html#associatedtype.Command)
associated type to
[`ConfigMap`](https://project-oak.github.io/oak/sdk/doc/oak/proto/oak/application/struct.ConfigMap.html):

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/aggregator/module/rust/src/lib.rs Rust /impl oak::CommandHandler/ /.*context.*/)
```Rust
impl oak::CommandHandler for Main {
    type Command = ConfigMap;

    fn handle_command(&mut self, command: ConfigMap) -> anyhow::Result<()> {
        let log_sender = oak::logger::create()?;
        oak::logger::init(log_sender.clone(), log::Level::Debug)?;
        let config: Config =
            toml::from_slice(command.items.get("config").expect("Couldn't find config"))
                .context("Couldn't parse TOML config file")?;
```
<!-- prettier-ignore-end -->

## Using an Oak Application from a client

A client that is outside of the Oak ecosystem can use an Oak Application by
interacting with it as a gRPC service, using the endpoint (host:port) from the
previous section (which would typically be published by the ISV providing the
Oak Application).

The client connects to the gRPC service, and sends (Application-specific) gRPC
requests to it, over a channel that has end-to-end encryption into the Runtime
instance, and also specifies a [Label](/docs/concepts.md#labels) to attach to
the request, which is used to enforce Information Flow Control within the
running Oak Application:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/hello_world/client/cpp/hello_world.cc C++ /.*Connect to the/ /GetTlsChannelCredentials.*/)
```C++
  // Connect to the Oak Application.
  auto stub = HelloWorld::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert_path), label));
```
<!-- prettier-ignore-end -->

Because the Oak Application is available as a gRPC service, clients written in
any language that supports gRPC can use the service. For example in Rust:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/private_set_intersection/client/rust/src/main.rs Rust /^.*create_client.*/ /^}/)
```Rust
async fn create_client(
    uri: &Uri,
    root_tls_certificate: &[u8],
    public_key: &[u8],
) -> anyhow::Result<
    PrivateSetIntersectionClient<
        InterceptedService<Channel, CombinedInterceptor<AuthInterceptor, LabelInterceptor>>,
    >,
> {
    info!("Connecting to Oak Application: {:?}", uri);
    let channel = create_tls_channel(uri, root_tls_certificate)
        .await
        .context("Couldn't create TLS channel")?;
    let label = confidentiality_label(web_assembly_module_signature_tag(public_key));
    let key_pair = oak_sign::KeyPair::generate()?;
    let interceptor = oak_client::interceptors::combine(
        AuthInterceptor::create(key_pair),
        LabelInterceptor::create(&label).context("Couldn't create gRPC interceptor")?,
    );
    Ok(PrivateSetIntersectionClient::with_interceptor(
        channel,
        interceptor,
    ))
}
```
<!-- prettier-ignore-end -->

Or for example in Go:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/translator/client/go/translator.go Go /.*Connect to the Oak/ /NewTranslatorClient.*/)
```Go
	// Connect to the Oak Application.
	creds, err := credentials.NewClientTLSFromFile(*caCert, "")
	if err != nil {
		glog.Exitf("Failed to set up TLS client credentials from %q: %v", *caCert, err)
	}
	// TODO(#1066): Use a more restrictive Label.
	label := label_pb.Label{}
	metadata, err := NewLabelMetadata(label)
	if err != nil {
		glog.Exitf("Failed to create label metadata for %v: %v", label, err)
	}
	conn, err := grpc.Dial(*address, grpc.WithTransportCredentials(creds), grpc.WithPerRPCCredentials(metadata))
	if err != nil {
		glog.Exitf("Failed to dial Oak Application at %v: %v", *address, err)
	}
	defer conn.Close()
	client := translator_pb.NewTranslatorClient(conn)
```
<!-- prettier-ignore-end -->

## gRPC Request Processing Path

At this point, the client code can interact with the Node code via gRPC. A
typical sequence for this (using the various helpers described in previous
sections) would be as follows:

- The Node code (Wasm code running in a Wasm interpreter, running in the Oak
  Runtime) is blocked inside a call to the `oak.wait_on_channels()` host
  function from the `oak::grpc::event_loop` helper function.
  - `event_loop()` was invoked directly from the `oak_main()` exported function.
- The client C++ code builds a gRPC request and sends it to the Oak Runtime.
  - This connection is end-to-end encrypted using TLS.
- The gRPC server pseudo-Node (which is part of the Oak Runtime) receives the
  message and encapsulates it in a `GrpcRequest` wrapper message.
- The gRPC server pseudo-Node serializes the `GrpcRequest` and writes it to the
  gRPC-in channel for the Node. It also creates a new channel for any responses,
  and passes a handle for this response channel alongside the request.
- This unblocks the Node code, and `oak::grpc::event_loop` reads and
  deserializes the incoming gRPC request. It then calls the `Dispatcher`'s
  `invoke()` method with the method name and (serialized) gRPC request.
- The auto-generated `Dispatcher` invokes the relevant method on the `Node`.
- The (user-written) code in this method does its work, and returns a response.
- The auto-generated `Dispatcher` struct encapsulates the response into a
  `GrpcResponse` wrapper message, and serializes into the response channel.
- The gRPC server pseudo-Node reads this message from the response channel,
  deserializes it and sends the inner response back to the client.
- The client C++ code receives the response.

<!-- From (Google-internal): http://go/sequencediagram/view/5741464478810112 -->
<img src="images/SDKFlow.png" width="850">

## Nodes, Channels and Handles

So far, we've only discussed writing a single Node for an Oak Application. This
Node communicates with the outside world via a single channel. The other half of
this single channel is a gRPC pseudo-Node, which passes on requests from
external clients (and which is automatically created by the Oak Runtime at
Application start-of-day).

More sophisticated Applications are normally built from multiple interacting
Nodes, for several reasons:

- Dividing software into well-defined interacting components is a normal way to
  reduce the overall complexity of software design.
- Software that handles sensitive data, or which has additional privileges,
  often separates out the parts that deal with this (the
  ["principle of least privilege"](https://en.wikipedia.org/wiki/Principle_of_least_privilege)),
  to reduce the blast radius if something goes wrong.
- Information flow analysis can be more precise and fine-grained if components
  are smaller and the interactions between them are constrained.

The first step in building a multi-Node Application is to write the code for all
of the Nodes; the `ApplicationConfiguration` needs to include the configuration
and code for any Node that might get run as part of the Application. New Node
types cannot be added after the application starts; any Node that the
Application might need has to be included in the original configuration.

As before, each Node must include a main entrypoint with signature
`fn(u64) -> ()`, but for an internal Node it's entirely up to the ISV as to what
channel handle gets passed to this entrypoint, and as to what messages are sent
down that channel. The application may choose to use protobuf-encoded messages
(as gRPC does) for its internal communications, or something else entirely (e.g.
the [serde crate](https://crates.io/crates/serde)).

Regardless of how the Application communicates with the new Node, the typical
pattern for the existing Node is to:

- Create a new channel with the
  [`channel_create`](https://project-oak.github.io/oak/sdk/doc/oak/fn.channel_create.html)
  host function, receiving local handles for both halves of the channel.
- Create a new Node instance with the
  [`node_create`](https://project-oak.github.io/oak/sdk/doc/oak/fn.node_create.html)
  host function, passing in the handle for the read half of the new channel.
- Afterwards, close the local handle for the read half, as it is no longer
  needed, and use the local handle for the write half to send messages to the
  new Node instance.

For example, the [example Chat application](../examples/chat) creates a Node for
each chat room and saves off the write handle that will be used to send messages
to the room:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/chat/module/rust/src/lib.rs Rust /.*self\.rooms\.entry\(/ /\}\);$/)
```Rust
                let channel = self.rooms.entry(label.clone()).or_insert_with(|| {
                    oak::io::entrypoint_node_create::<Room, _, _>(
                        "room",
                        &label,
                        "app",
                        LogInit { log_sender },
                    )
                    .expect("could not create room node")
                });
```
<!-- prettier-ignore-end-->

The same code (identified by `"room-config"`) will be run for each per-room
Node, but each instance will have its own Web Assembly linear memory (≈heap) and
stack.

The `node_create()` call triggers the Oak Runtime to invoke the main entrypoint
for the new Node (as specified in the Application configuration), passing in the
handle value for the channel read half that was provided as a parameter to
`node_create()`. Note that the actual handle _value_ passed into the main
entrypoint will (almost certainly) be different; internally, the Runtime
translates the creator Node's handle value to a reference to the underlying
channel object, then assigns a new numeric value for the created Node to use to
refer to the underlying channel.

Once a new Node has started, the existing Node can communicate with the new Node
by sending messages over the channel via `channel_write` (or
`channel_write_with_downgrade` if the label downgrading is required). Of course,
the new Node only has a handle to the read half of a channel, and so only has a
way of _receiving_.

To cope with this, it's normal for the inbound messages to be accompanied by a
handle for the _write_ half of a different channel, which is then used for
responses &ndash; so the new Node has a way of _sending_ externally, as well as
receiving.

For Nodes that communicate by exchanging messages that are serialized protocol
buffer messages, the Oak SDK allows encoding channel handles into protobuf
messages:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/injection/proto/injection.proto Protobuf /^message BlobStoreSender/ /^}$/)
```Protobuf
message BlobStoreSender {
  oak.handle.Sender sender = 1 [(oak.handle.message_type) = ".oak.examples.injection.BlobResponse"];
}
```
<!-- prettier-ignore-end -->

The `message_type` field option provided by the SDK specifies the fully
qualified (with leading dot) name of the protobuf message passed over the
channel.

The above protobuf definition generates the following Rust data type:

```Rust
struct BlobStoreSender {
  sender: ::oak_io::Sender<BlobResponse>,
}
```

An `oak.handle.Receiver` type is also available for read handles.

The generated struct is fully type safe, encoding the direction of the handle
(`Sender` or `Receiver`) as well as the type of the message that is sent or
received using `message_type`.

## Persistent Storage

TODO: describe use of storage

## Using External gRPC Services

To allow Oak applications connect to external gRPC services, the Oak SDK
provides a convenient API for creating gRPC Client pseudo nodes:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/aggregator/module/rust/src/lib.rs Rust /.*let grpc_client_invocation_sender.*/ /gRPC client.*/)
```Rust
        let grpc_client_invocation_sender = oak::grpc::client::init(&config.backend_server_address)
            .context("Couldn't create gRPC client")?;
```
<!-- prettier-ignore-end -->

The client is initialized with the `address` of the external gRPC service (e.g.,
`https://localhost:8888`). The `init` method returns a handle to a channel that
can be used for sending invocations to the client pseudo node. With this handle
gRPC client stub can be created, as in the `Aggregator` example:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/aggregator/module/rust/src/handler.rs Rust /.*oak::WithInit/ /^}$/)
```Rust
impl oak::WithInit for Handler {
    type Init = HandlerInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        let grpc_client_invocation_sender = init
            .grpc_client_invocation_sender
            .expect("Couldn't receive gRPC invocation sender")
            .sender
            .expect("Empty gRPC invocation sender");

        Self::new(grpc_client_invocation_sender)
    }
}
```
<!-- prettier-ignore-end -->

The call to `Self::new` above creates an instance of `AggregatorClient`
initialized with the write-half of the channel to the gRPC client pseudo node:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/aggregator/module/rust/src/handler.rs Rust /.*fn new/ /^    }$/)
```Rust
    fn new(invocation_sender: Sender<grpc::Invocation>) -> Self {
        Self {
            backend_client: AggregatorClient(invocation_sender),
            aggregators: HashMap::new(),
        }
    }
```
<!-- prettier-ignore-end -->

## Using External HTTP Services

An Oak application may need to interact with external services. This can be done
using an HTTP client pseudo node. The Oak SDK provides a convenient API for
creating HTTP Client pseudo nodes:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/http_server/module/src/lib.rs Rust /.*let client_invocation_sender.*/)
```Rust
    let client_invocation_sender = oak::http::client::init("localhost:8080").unwrap();
```
<!-- prettier-ignore-end -->

The input parameter to `init` is the authority of the server that the Oak
application needs to connect to. If an empty string is passed as the authority,
then this client node can connect to any external server. Otherwise, the HTTP
client pseudo node can only connect to the server specified by the given
authority over HTTPS. The `init` method returns a handle to a channel that can
be used for sending invocations to the client pseudo node. From there you can
create normal HTTP requests and send them via the client pseudo node:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/http_server/module/src/lib.rs Rust /.*http::Req/ /HTTP client.*;$/)
```Rust
        let request = http::Request::builder()
            .method(http::Method::GET)
            .uri("https://localhost:8080")
            .header(oak_abi::OAK_LABEL_HTTP_JSON_KEY, label_bytes)
            .body(vec![])
            .context("Couldn't build request")?;

        // Send the request to the HTTP client pseudo-Node
        client_invocation
            .send(request)
            .context("Couldn't send the request to the HTTP client")?;
```
<!-- prettier-ignore-end -->

## Testing

> "Beware of bugs in the above code; I have only proved it correct, not tried
> it." - [Donald Knuth](https://www-cs-faculty.stanford.edu/~knuth/faq.html)

Regardless of how the code for an Oak Application is produced, it's always a
good idea to write tests. The
[`oak_tests`](https://project-oak.github.io/oak/sdk/doc/oak_tests/index.html)
crate allows Node gRPC service methods to be tested with the [Oak SDK](sdk.md)
framework via the Oak Runtime:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/translator/module/rust/tests/integration_test.rs Rust /#\[tokio/ /^}$/)
```Rust
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn test_translate() {
    let _ = env_logger::builder().is_test(true).try_init();
    let permissions = oak_runtime::permissions::PermissionsConfiguration {
        allow_grpc_server_nodes: true,
        allow_log_nodes: true,
        ..Default::default()
    };

    let runtime = oak_tests::run_single_module_default(permissions)
        .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::public_channel_and_interceptor().await;
    let mut client = TranslatorClient::with_interceptor(channel, interceptor);

    let req = TranslateRequest {
        text: "WORLDS".into(),
        from_lang: "en".into(),
        to_lang: "it".into(),
    };
    info!("Sending request: {:?}", req);

    let result = client.translate(req).await;
    assert_matches!(result, Ok(_));
    assert_eq!("MONDI", result.unwrap().into_inner().translated_text);

    runtime.stop();
}
```
<!-- prettier-ignore-end -->

This has a little bit of boilerplate to explain:

- The
  [`oak_tests`](https://project-oak.github.io/oak/sdk/doc/oak_tests/index.html)
  crate provides a
  [`run_single_module_default`](https://project-oak.github.io/oak/sdk/doc/oak_tests/fn.run_single_module_default.html)
  method that is designed for use with single-Node Applications. It assumes that
  the Node has a main entrypoint called `oak_main`, which it runs in a separate
  thread.
- The
  [`oak_tests::public_channel_and_interceptor`](https://project-oak.github.io/oak/sdk/doc/oak_tests/fn.public_channel_and_interceptor.html)
  method returns a gRPC
  [`Channel`](https://docs.rs/tonic/0.3.1/tonic/transport/channel/struct.Channel.html)
  that can be used to send requests to the Application under test
- The per-Node thread needs to be stopped at the end of the test
  ([`oak_runtime::Runtime::stop`](https://project-oak.github.io/oak/oak_runtime/doc/oak_runtime/struct.Runtime.html#method.stop)).

[`oak_tests`](https://project-oak.github.io/oak/sdk/doc/oak_tests/index.html)
additionally exposes a
[`runtime_config_wasm`](https://project-oak.github.io/oak/sdk/doc/oak_tests/fn.runtime_config_wasm.html)
method that allows configuring more complex Applications with multiple Nodes,
like in the following example:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/hello_world/module/rust/tests/integration_test.rs Rust /^.*Test invoking the SayHello Node service method via the Oak runtime.*/ /^}$/)
```Rust
// Test invoking the SayHello Node service method via the Oak runtime.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn test_say_hello() {
    let _ = env_logger::builder().is_test(true).try_init();
    let permissions = oak_runtime::permissions::PermissionsConfiguration {
        allow_grpc_server_nodes: true,
        allow_log_nodes: true,
        ..Default::default()
    };
    let runtime_config = oak_tests::runtime_config_wasm(
        hashmap! {
            MAIN_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(MAIN_MODULE_MANIFEST, oak_tests::Profile::Release).expect("Couldn't compile main module"),
            TRANSLATOR_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(TRANSLATOR_MODULE_MANIFEST, oak_tests::Profile::Release).expect("Couldn't compile translator module"),
        },
        MAIN_MODULE_NAME,
        MAIN_ENTRYPOINT_NAME,
        ConfigMap::default(),
        permissions,
        oak_runtime::SignatureTable::default(),
    );
    let runtime = oak_runtime::configure_and_run(runtime_config)
        .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::public_channel_and_interceptor().await;
    let mut client = HelloWorldClient::with_interceptor(channel, interceptor);

    {
        let req = HelloRequest {
            greeting: "world".into(),
        };
        info!("Sending request: {:?}", req);
        let result = client.say_hello(req.clone()).await;
        assert_matches!(result, Ok(_));
        assert_eq!("HELLO world!", result.unwrap().into_inner().reply);
    }
    {
        let req = HelloRequest {
            greeting: "WORLDS".into(),
        };
        info!("Sending request: {:?}", req);
        let result = client.lots_of_replies(req).await;
        assert_matches!(result, Ok(_));
        // Make sure that the translated response was received.
        assert_eq!(
            vec![
                HelloResponse {
                    reply: "HELLO WORLDS!".to_string()
                },
                HelloResponse {
                    reply: "BONJOUR MONDES!".to_string()
                },
                HelloResponse {
                    reply: "HELLO AGAIN WORLDS!".to_string()
                },
            ],
            result
                .unwrap()
                .into_inner()
                .collect::<Vec<Result<HelloResponse, tonic::Status>>>()
                .await
                .into_iter()
                .filter_map(Result::ok)
                .collect::<Vec<HelloResponse>>()
        );
    }

    runtime.stop();
}
```
<!-- prettier-ignore-end -->

## Debugging and introspection

For debugging purposes, the `oak_loader` could be built with the `oak_unsafe`
feature. This feature enables logs, and exposes an introspection server on
`localhost` that by default is served on port `1909`.
