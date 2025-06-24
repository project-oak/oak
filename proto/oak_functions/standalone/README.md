# Oak Functions Standalone

We provide a standalone Oak Functions service which can run as its own binary.
Unlike the service provided in
oak/proto/oak_functions/service/oak_functions.proto, this service exclusively
focuses on handling user facing requests over a bidirectional streaming
interface. This service does not expose any methods regarding the WASM and
attestation initialization nor the chunking and loading of lookup data. Such
steps are expected to be done as part of the server startup.

This service relies on the Noise NN Protocol for communicating with clients.
Refer to the oak/oak_session folder for details.
