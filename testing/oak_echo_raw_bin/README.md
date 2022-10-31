# Oak Echo Raw

Echo freestanding binary that can be run under
[crosvm](https://chromium.googlesource.com/chromiumos/platform/crosvm/).

Echo binary receives a message as bytes, and sends back the same bytes, without
interpreting them.

This binary doesn't use IDL to communicate between the Untrusted Launcher and
the guest VM, but instead uses a raw SimpleIO channel. The binary is used
primarily for Vanadium tests.
