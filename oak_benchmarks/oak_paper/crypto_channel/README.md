# Oak Session Crypto Channel Performance Evaluation

This is a set of communications/crypto channel evaluations for Oak Restricted
Kernel.

It uses a very simple protocol to minimize additional overhead, focusing only on
a basic comms channel and encryption protocol.

We have a simple read/write server implementation for restricted kernel, as well
as for Linux, using a plain TCP socket + our simple protocol.

The underlying protocol is just a length-prefixed blob of bytes.

We currently test the following combinations:

- Plaintext protocol, Local TCP Server
- NoiseNN encrypted protocol, Local TCP Server
- Plaintext protocol, Restricted Kernel Server
- NoiseNN encrypted protocol, Restricted Kernel Server
