# Oak Echo

Echo freestanding binary that can be run under
[crosvm](https://chromium.googlesource.com/chromiumos/platform/crosvm/).

Echo binary receives a microRPC request containing bytes, and sends back a
microRPC response with the same bytes, without interpreting them.

This binary uses microRPC to communicate between the Untrusted Launcher and the
guest VM. The interface is defined in
[`oak_echo.proto`](testing/oak_echo_service/oak_echo.proto).
