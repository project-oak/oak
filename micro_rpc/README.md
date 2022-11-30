# microRPC

microRPC is a minimal IPC / RPC framework that uses
[Protocol Buffers](https://developers.google.com/protocol-buffers) as the IDL to
define messages and services, and it generates client and server stubs that
operate over an abstract low-level transport mechanism.

For each service definition, and for each target language (currently only Rust),
microRPC generates:

- a client object
- a server object

Additionally, the regular protobuf compiler is invoked to generate objects
corresponding to individual messages; these are not specific to microRPC and
follow standard protobuf format and APIs.

The client and server objects can connect to each other over a transport. A
transport consists of a single method, usually called `invoke`, which represents
an atomic invocation, sending a sequence of bytes and receiving a sequence of
bytes. microRPC takes care of translating a call on the client object to a
request messsage, serialize that to bytes, then on the server side deserialize
the bytes into the request message, and dispatching the user request to the
correct method on the server object, and similarly for the response path back to
the client.

See [the microRPC Rust library](/micro_rpc/src/lib.rs) for the definition of
Transport in Rust.

See [an example generated file](/micro_rpc_tests/out/micro_rpc.tests.rs.txt).
