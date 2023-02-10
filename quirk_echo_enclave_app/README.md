# Oak Echo

Echo enclave application that can be run under Restricted Kernel.

Echo binary receives a microRPC request containing bytes, and sends back a
microRPC response with the same bytes, without interpreting them.

This binary uses microRPC to communicate between the Untrusted Launcher and the
guest VM. The interface is defined in
[`quirk_echo.proto`](quirk_echo_service/proto/quirk_echo.proto).
