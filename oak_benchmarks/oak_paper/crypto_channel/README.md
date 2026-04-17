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

All measurements are taken on the host side.

- In general, we are interested in relative latencies rather than absolute
  latencies, so consistency between the test types is important.
- To compare handshake latencies, we use tests where the server sends a single
  byte of data after its handshake.
- In tests that measure sending speeds, a short ACK from the server is used to
  indicate complete reception of the data.
- In tests that measure receive speeds, the host measures the time it takes to
  receive the expected amount of data.
