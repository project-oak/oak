# Noise protocol handshake.

This is a port from Google's internal enclave app repo, which was approved for
open sourcing.

* (The noise framework)[http://www.noiseprotocol.org/noise.html]
* (Noise explorer)[https://noiseexplorer.com/patterns/NK/]

In general, when communicating secrets to an enclave, it is recommended to use
one of the well-reviewed noise variants for multi-round communication between
clients and servers, and HPKE for launch-and-forget style requests.

Currently only noise-NK is supported, but a future PR is planned for adding noise-NN support.
