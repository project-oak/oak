# Experimental UEFI app and untrusted loader

This directory contains a bare-bones UEFI app and an "untrusted loader" built
around `qemu` that communicates with said app. The goal of the experiment is to
try out different communication mechanisms etc to see how Oak could run in a
trusted environment as an UEFI app with minimal dependencies, with code that
doesn't need to be trusted left outside the trusted environment.

To run:

- build the UEFI app (note that the app is not part of the normal workspace
  because of #2654)
- run
  `RUST_LOG=info cargo run -- /workspace/experimental/uefi/app/target/x86_64-unknown-uefi/debug/uefi-simple.efi`
  (note that the path assumes you're in the dev container)

This will start `qemu` and wire up the sockets. Any input (remember to press
enter) will be sent to the app, which will dutifully echo it back.

To quit, press `^C`; you may need to press an extra Enter for the process to
actually terminate because consoles are hard.

## UEFI app

The UEFI app assumes that there's two serial ports on the system:

- the first one will be used for UEFI stdio and any logs produced by the app
- the second serial port is used by the app to echo back every byte written to
  it.

## Untrusted loader

The loader wraps `qemu` and sets up the plumbing to communicate with the UEFI
app.

- any output to the first serial port will be logged
- communication over the second serial port will also be logged
- any input to stdin will be sent to the UEFI app.
