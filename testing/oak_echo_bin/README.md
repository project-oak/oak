# Oak Echo

Echo freestanding binary that can be run under
[crosvm](https://chromium.googlesource.com/chromiumos/platform/crosvm/).

Echo binary receives an IDL request containing bytes, and sends back an IDL
response with the same bytes, without interpreting them.

This binary uses IDL to communicate between the Untrusted Launcher and the guest
VM. The interface is defined here:
[`schema.fbs`](testing/oak_echo_service/schema.fbs)
