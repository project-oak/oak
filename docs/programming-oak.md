# Programming Oak

This document walks through the basics of programming in Oak.

- [Writing an Oak Node](#writing-an-oak-node)
  - [Per-Node Boilerplate](#per-node-boilerplate)
  - [Generated gRPC service code](#generated-grpc-service-code)
- [Using an Oak Application from a client](#using-an-oak-application-from-a-client)
  - [Connecting to the Oak Manager](#connecting-to-the-oak-manager)
  - [Starting the Oak Application](#starting-the-oak-application)
- [gRPC Request Processing Path](#grpc-request-processing-path)
- [Node Termination](#node-termination)
- [Nodes, Channels and Handles](#nodes-channels-and-handles)
- [Persistent Storage](#persistent-storage)
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

An Oak Node needs to provide a single
[main entrypoint](abi.md#exported-function), which is the point at which Node
execution begins. However, Node authors don't _have_ to implement this function
themselves; for a Node which is triggered by external gRPC requests (the normal
"front door" for an Oak application), there are helper functions in the Oak SDK
that make this easier.

To use these helpers, an Oak Node should implement a `struct` of some kind to
represent the Node itself, and then add the `derive(OakExports)` attribute (from
the [`oak_derive`](https://project-oak.github.io/oak/sdk/oak_derive/index.html)
crate):

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/rustfmt/module/rust/src/lib.rs Rust /.*derive\(OakExports\).*]/ /;$/)
```Rust
#[derive(OakExports)]
struct Node;
```
<!-- prettier-ignore-end -->

If the Node needs per-instance state, this Node `struct` is an ideal place to
store it. For example, the running average example has a `Node` `struct` with a
running sum and count of samples:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/running_average/module/rust/src/lib.rs Rust /.*derive\(Default, OakExports\).*]/ /^}/)
```Rust
#[derive(Default, OakExports)]
struct Node {
    sum: u64,
    count: u64,
}
```
<!-- prettier-ignore-end -->

Under the covers the
[`derive(OakExports)`](https://project-oak.github.io/oak/sdk/oak_derive/derive.OakExports.html)
macro implements a main function named `oak_main` for you, with the following
default behaviour:

- Create an instance of your Node `struct` (using the `new()` method from the
  [`OakNode`](https://project-oak.github.io/oak/sdk/oak/grpc/trait.OakNode.html)
  trait described below).
- Take the channel handle passed to `oak_main()` and use it for gRPC input.
- Pass the Node `struct` and the channel handle to the
  [`event_loop()`](https://project-oak.github.io/oak/sdk/oak/grpc/fn.event_loop.html)
  function from the [`oak::grpc` module](sdk.md#oakgrpc-module).

To make this work, the Node `struct` must implement the
[`oak::grpc::OakNode`](https://project-oak.github.io/oak/sdk/oak/grpc/trait.OakNode.html)
trait. This has two methods:

- A
  [`new()`](https://project-oak.github.io/oak/sdk/oak/grpc/trait.OakNode.html#tymethod.new)
  method to create an instance of the Node, and perform any one-off
  initialization. (A common initialization action is to enable logging for the
  Node, via the [`oak_log` crate](sdk.md#oak_log-crate).)
- An
  [`invoke()`](https://project-oak.github.io/oak/sdk/oak/grpc/trait.OakNode.html#tymethod.invoke)
  method that is called for each newly-arriving gRPC request from the outside
  world.

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/rustfmt/module/rust/src/lib.rs Rust /impl oak::grpc::OakNode/ /^}/)
```Rust
impl oak::grpc::OakNode for Node {
    fn new() -> Self {
        oak_log::init_default();
        Node
    }
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}
```
<!-- prettier-ignore-end -->

The `invoke` method can be written manually, but it is usually easier to rely on
code that is auto-generated from a gRPC service definition, described in the
next section.

### Generated gRPC service code

The Oak SDK includes a `proto_rust_grpc` tool (forked from
https://github.com/stepancheg/rust-protobuf) which takes a
[gRPC service definition](https://grpc.io/docs/guides/concepts/) and
autogenerates Rust code for the corresponding Oak Node that implements that
service.

Adding a `build.rs` file to the Node that invokes this tool results in a
generated file appearing in `src/proto/<service>_grpc.rs`.

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/hello_world/module/rust/build.rs Rust /fn main/ /^}/)
```Rust
fn main() {
    protoc_rust_grpc::run(protoc_rust_grpc::Args {
        out_dir: "src/proto",
        input: &["../../proto/hello_world.proto"],
        includes: &["../../proto", "../../third_party"],
        rust_protobuf: true, // also generate protobuf messages, not just services
        ..Default::default()
    })
    .expect("protoc-rust-grpc");
}
```
<!-- prettier-ignore-end -->

The autogenerated code includes two key chunks.

The first is a trait definition that includes a method for each of the methods
in the gRPC service, taking the relevant (auto-generated) request and response
types. The Oak Node implements the gRPC service by implementing this trait.

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/rustfmt/module/rust/src/proto/rustfmt_grpc.rs Rust /pub trait FormatServiceNode/ /^}/)
```Rust
pub trait FormatServiceNode {
    fn format(&mut self, req: super::rustfmt::FormatRequest) -> grpc::Result<super::rustfmt::FormatResponse>;
}
```
<!-- prettier-ignore-end -->

Secondly, the autogenerated code includes a `dispatch()` method which maps a
request (as a method name and encoded request) to an invocation of the relevant
method on the service trait. This `dispatch()` method can then form the entire
implementation of the `OakNode::invoke()` method described in the previous
section.

Taken altogether, this covers all of the boilerplate needed to have a Node act
as a gRPC server:

- The main `oak_main` entrypoint is auto-generated, and invokes
  `oak::grpc::event_loop` with a new Node `struct`.
- This Node `struct` implements `oak::grpc::OakNode` so the `event_loop()`
  method can call back into the Node's `invoke()` method.
- The `invoke()` method typically just forwards on to the `dispatch()` method
  from the per-gRPC-service auto-generated code.
- The auto-generated `dispatch()` method invokes the relevant per-service method
  of the Node, available because the Node `struct` implements the gRPC service
  trait.

## Using an Oak Application from a client

A client that is outside of the Oak ecosystem can use an Oak Application by
interacting with it as a gRPC service. However, this does involve a few
additional complications beyond the normal gRPC boilerplate, which are described
in this section.

### Connecting to the Oak Manager

Oak client code (in C++) first needs to connect to the
[Oak Manager](concepts.md#oak-manager), as a normal gRPC client:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/abitest/client/abitest.cc C++ /.*Connect to the Oak Manager/ /NewStub.*;/)
```C++
  // Connect to the Oak Manager.
  auto channel =
      grpc::CreateChannel(absl::GetFlag(FLAGS_manager_address), grpc::InsecureChannelCredentials());
  auto manager_stub = oak::Manager::NewStub(channel, grpc::StubOptions());
```
<!-- prettier-ignore-end -->

This sets up a client for the `oak.Manager` service; this service allows the
creation and termination of Oak Applications:

<!-- prettier-ignore-start -->
[embedmd]:# (../oak/proto/manager.proto protobuf /^service Manager/ /^}/)
```protobuf
service Manager {
  // Request the creation of a new Oak Application with the specified configuration.
  //
  // After the Oak Node is created, the client should connect to the returned
  // endpoint via gRPC and perform a direct attestation against the Node itself,
  // to verify that its configuration corresponds to what the client expects.
  rpc CreateApplication(CreateApplicationRequest) returns (CreateApplicationResponse);

  // Request that an Oak Application terminate.
  rpc TerminateApplication(TerminateApplicationRequest) returns (TerminateApplicationResponse);
}
```
<!-- prettier-ignore-end -->

Alternatively, the manager client can also be wrapped up in a
[helper library](../oak/client/manager_client.h), which will make application
configuration (described in the next section) easier:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/rustfmt/client/rustfmt.cc C++ /.*Connect to the Oak Manager/ /FLAGS_manager_address.*;/)
```C++
  // Connect to the Oak Manager.
  std::unique_ptr<oak::ManagerClient> manager_client =
      absl::make_unique<oak::ManagerClient>(grpc::CreateChannel(
          absl::GetFlag(FLAGS_manager_address), grpc::InsecureChannelCredentials()));
```
<!-- prettier-ignore-end -->

### Starting the Oak Application

To use the `CreateApplication` method, the client needs to specify the
_application configuration_; this describes the Nodes that make up the
application, and the initial Node to start. However, for the simple case of a
one-Node application the `oak::ManagerClient` helper takes care of this; the
client just need to provide the code that is going to be run in the Node, as a
Wasm module:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/rustfmt/client/rustfmt.cc C++ /.*FLAGS_module/ /}/)
```C++
  std::string module_bytes = oak::utils::read_file(absl::GetFlag(FLAGS_module));
  std::unique_ptr<oak::CreateApplicationResponse> create_application_response =
      manager_client->CreateApplication(module_bytes);
  if (create_application_response == nullptr) {
    LOG(QFATAL) << "Failed to create application";
  }
```
<!-- prettier-ignore-end -->

There's also a variant of `CreateApplication` that allows the client code to
specify a storage provider to connect to, and to control whether logging is
enabled:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/hello_world/client/hello_world.cc C++ /.*FLAGS_module/ /}/)
```C++
  std::string module_bytes = oak::utils::read_file(absl::GetFlag(FLAGS_module));
  std::unique_ptr<oak::CreateApplicationResponse> create_application_response =
      manager_client->CreateApplication(module_bytes, /* logging= */ true,
                                        absl::GetFlag(FLAGS_storage_address));
  if (create_application_response == nullptr) {
    LOG(QFATAL) << "Failed to create application";
  }
```
<!-- prettier-ignore-end -->

The Oak Manager will launch an [Oak Runtime](concepts.md#oak-vm) inside the
enclave, and this Runtime will check the provided Wasm module(s) and application
configuration. Assuming everything is correct (e.g. the Nodes all have a main
entrypoint and only expect to find the Oak
[host functions](abi.md#host-functions)), the Oak Runtime opens up a port of its
own and the `CreateApplication` returns this to the client.

The client can now connect to this separate gRPC service, and send
(Node-specific) gRPC requests to it, over a channel that has end-to-end
encryption into the enclave:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/rustfmt/client/rustfmt.cc C++ /.*InitializeAssertionAuthorities/ /CreateChannel.*/)
```C++
  oak::ApplicationClient::InitializeAssertionAuthorities();

  // Connect to the newly created Oak Application.
  auto stub = FormatService::NewStub(oak::ApplicationClient::CreateChannel(addr.str()));
```
<!-- prettier-ignore-end -->

## gRPC Request Processing Path

At this point, the client code can interact with the Node code via gRPC. A
typical sequence for this (using the various helpers described in previous
sections) would be as follows:

- The Node code (Wasm code running in a Wasm interpreter, running in an enclave)
  is blocked inside a call to the `oak.wait_on_channels()` host function from
  the `oak::grpc::event_loop` helper function.
  - `event_loop()` was invoked directly from the auto-generated `oak_main()`
    exported function.
- The client C++ code builds a gRPC request and sends it to the Oak Runtime.
  - This connection is end-to-end encrypted using the Asylo key exchange
    mechanism.
- The Oak Runtime receives the message and encapsulates it in a `GrpcRequest`
  wrapper message.
- The Oak Runtime serializes the `GrpcRequest` and writes it to the gRPC-in
  channel for the node. It also creates a new channel for any responses, and
  passes a handle for this response channel alongside the request.
- This unblocks the Node code, and `oak::grpc::event_loop` reads and
  deserializes the incoming gRPC request. It then calls the Node's `invoke()`
  method with the method name and (serialized) gRPC request.
- The Node's `invoke()` method passes this straight on to the auto-generated
  gRPC service code in `proto::service_name_grpc::dispatch()`.
- The auto-generated `dispatch()` code invokes the relevant method on the
  `Node`.
- The (user-written) code in this method does its work, and returns a response.
- The auto-generated `dispatch()` code encapsulates the response into a
  `GrpcResponse` wrapper message, and serializes into the response channel.
- The Oak Runtime reads this message from the response channel, deserializes it
  and sends the inner response back to the client.
- The client C++ code receives the response.

<!-- From (Google-internal): http://go/sequencediagram/view/5741464478810112 -->
<img src="images/SDKFlow.png" width="850">

## Node Termination

The client can also politely request that the Oak Application terminate, using
the `TerminateApplication` method on the (outer) gRPC service. The Oak Manager
passes this on to the Oak Runtime, which will then notify the running Nodes that
termination has been requested (by returning `ERR_TERMINATED` on any current or
future `oak.wait_on_channels()` invocations).

## Nodes, Channels and Handles

So far, we've only discussed writing a single Node for an Oak Application. This
Node communicates with the outside world via a single channel, and the handle
for the read half of this channel is acquired at start-of-day as the parameter
to the `oak_main()` entrypoint. The other half of this single channel is a gRPC
pseudo-Node, which passes on requests from external clients (and which is
automatically created by the Oak Runtime at Application start-of-day).

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
`(u64) -> u32`, but for an internal Node it's entirely up to the Application
developer as to what channel handle gets passed to this entrypoint, and as to
what messages are sent down that channel. The application may choose to use
protobuf-encoded messages (as gRPC does) for its internal communications, or
something else entirely (e.g. the
[serde crate](https://crates.io/crates/serde)).

Regardless of how the application communicates with the new Node, the typical
pattern for the existing Node is to:

- Create a new channel with the
  [`channel_create`](https://project-oak.github.io/oak/sdk/oak/fn.channel_create.html)
  host function, receiving local handles for both halves of the channel.
- Create a new Node instance with the
  [`node_create`](https://project-oak.github.io/oak/sdk/oak/fn.node_create.html)
  host function, passing in the handle for the read half of the new channel.
- Afterwards, close the local handle for the read half, as it is no longer
  needed.

For example, the [example Chat application](../examples/chat) creates a Node for
each chat room and saves off the write handle that will be used to send messages
to the room:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/chat/module_0/rust/src/lib.rs Rust /.*channel_create\(\)/ /\}$/)
```Rust
        let (wh, rh) = oak::channel_create().unwrap();
        oak::node_create("room-config", rh).expect("could not create node");
        oak::channel_close(rh.handle).expect("could not close channel");
        Room {
            sender: oak::io::Sender::new(wh),
            admin_token,
        }
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
by sending messages over the channel via `channel_write`. Of course, the new
Node only has a handle to the read half of a channel, and so only has a way of
_receiving_.

To cope with this, it's normal for the inbound messages to be accompanied by a
handle for the _write_ half of a different channel, which is then used for
responses &ndash; so the new Node has a way of _sending_ externally, as well as
receiving.

## Persistent Storage

TODO: describe use of storage

## Testing

> "Beware of bugs in the above code; I have only proved it correct, not tried
> it." - [Donald Knuth](https://www-cs-faculty.stanford.edu/~knuth/faq.html)

Regardless of how the code for an Oak Application is produced, it's always a
good idea to write tests for any software. For an Oak Node that
[implements a gRPC service](#generated-grpc-service-code) purely internally,
it's straightforward to test the methods of the service just by calling them:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/hello_world/module/rust/src/tests.rs Rust /^.*Test invoking a Node service method directly.*/ /^}$/)
```Rust
// Test invoking a Node service method directly.
#[test]
fn test_direct_hello_request() {
    let mut node = crate::Node::new();
    let mut req = HelloRequest::new();
    req.set_greeting("world".to_string());
    let result = node.say_hello(req);
    assert_matches!(result, Ok(_));
    assert_eq!("HELLO world!", result.unwrap().reply);
}
```
<!-- prettier-ignore-end -->

The [oak_tests](https://project-oak.github.io/oak/sdk/oak_tests/index.html)
crate also allows the gRPC service methods to be tested via the
[Oak SDK](sdk.md) framework:

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/hello_world/module/rust/src/tests.rs Rust /^.*Test invoking a Node service method via the Oak.*/ /^}$/)
```Rust
// Test invoking a Node service method via the Oak entrypoints.
#[test]
#[serial(node_test)]
fn test_hello_request() {
    let handle = oak_tests::grpc_channel_setup_default();
    oak_tests::start_node(handle);

    let mut req = HelloRequest::new();
    req.set_greeting("world".to_string());
    let result: grpc::Result<HelloResponse> =
        oak_tests::inject_grpc_request("/oak.examples.hello_world.HelloWorld/SayHello", req);
    assert_matches!(result, Ok(_));
    assert_eq!("HELLO world!", result.unwrap().reply);

    assert_eq!(Err(OakStatus::ERR_TERMINATED), oak_tests::stop());
}
```
<!-- prettier-ignore-end -->

This has a little bit more boilerplate than testing a method directly:

- The inbound gRPC channel that requests are delivered over has to be explicitly
  set up (`oak_tests::grpc_channel_setup_default`)
- A separate thread running the Node's main entrypoint (assumed to be called
  `oak_main`, which is the name that the
  [`derive(OakExports)`](https://project-oak.github.io/oak/sdk/oak_derive/derive.OakExports.html)
  macro creates) is started (`oak_tests::start_node`).
- The injection of the gRPC request has to specify the method name (in
  `oak_tests::inject_grpc_request`).
- The per-Node thread needs to be stopped at the end of the test
  (`oak_tests::stop`).
- Because the Node's `oak_main` entrypoint should only be running in a single
  thread, we use the [serial_test](https://crates.io/crates/serial_test) crate
  to mark that the test should be serialized with any other tests that involve
  the node (`#[serial(node_test)]`).

However, this extra complication does allow the Node to be tested in a way that
is closer to real execution, and (more importantly) allows testing of a Node
that makes use of the functionality of the Oak TCB.

### Testing Multi-Node Applications

It's also possible to test an Oak Application that's built from multiple Nodes,
using the `oak_tests::start()` entrypoint. The first argument to this entrypoint
is an `ApplicationConfiguration` protobuf message, the same as is needed for
normally [starting the Oak Application](#starting-the-oak-application) (except
now in Rust rather than C++).

However, the fields in the application configuration that hold the Wasm bytecode
for the various Nodes are ignored; instead, the second argument to
`oak_tests::start()` is a map from the relevant `NodeContents.name` to a
function pointer of type `oak_runtime::NodeMain` that acts as the main
entrypoint for the Node under test. This inner test entrypoint is intended for
use from Rust test code, and so has a signature
(`fn(u64) -> Result<(), oak::OakStatus>`) which allows for better error handling
than the signature (`fn(u64) -> i32`) that is available for the real Wasm
entrypoint.

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/abitest/tests/src/tests.rs Rust /^#\[test\]/ /oak_tests::start\(.*/)
```Rust
#[test]
#[serial(node_test)]
fn test_abi() {
    // Initialize the test logger first, so logging gets redirected to simple_logger.
    // (A subsequent attempt to use the oak_log crate will fail.)
    oak_tests::init_logging();
    let mut entrypoints = HashMap::new();
    let fe: oak_runtime::NodeMain = abitest_0_frontend::main;
    let be: oak_runtime::NodeMain = abitest_1_backend::main;
    entrypoints.insert(FRONTEND_CONFIG_NAME.to_string(), fe);
    entrypoints.insert(BACKEND_CONFIG_NAME.to_string(), be);
    assert_eq!(Some(()), oak_tests::start(test_config(), entrypoints));
```
<!-- prettier-ignore-end -->

Because there are multiple Nodes linked into the whole Application under test,
each Node should use a [main entrypoint](abi.md#exported-function) with a
different name, to prevent their names clashing.

The inner main functionality described above also allows
[panic interception for FFI](https://doc.rust-lang.org/nomicon/ffi.html#ffi-and-panics)
to be localized to the real Wasm entrypoint; testing via the inner main
therefore allows panic conditions to be tested more easily.

<!-- prettier-ignore-start -->
[embedmd]:# (../examples/abitest/module_0/rust/src/lib.rs Rust /^#.*no_mangle.*/ /pub fn main\(.*/)
```Rust
#[no_mangle]
pub extern "C" fn frontend_oak_main(handle: u64) -> i32 {
    std::panic::catch_unwind(|| main(handle))
        .unwrap_or(Err(oak::OakStatus::ERR_INTERNAL))
        .err()
        .unwrap_or(oak::OakStatus::OK)
        .value()
}

pub fn main(handle: u64) -> Result<(), oak::OakStatus> {
```
<!-- prettier-ignore-end -->

This allows the
[`catch_unwind`](https://doc.rust-lang.org/std/panic/fn.catch_unwind.html)
protection to be localized to the main entrypoint that the real Oak Runtime
invokes, where it's particularly needed to prevent panic crossing the Wasm FFI
boundary. The inner main is used for testing (and so needs to be `pub`), and
_does_ allow panics to propagate to the tests &ndash; which is helpful for
debugging.

The overall test then lives in a crate of its own, which imports the individual
crates for the different Oak Nodes, and uses `oak_tests::start` to assemble
different threads running the per-Node entrypoints.
