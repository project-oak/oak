# Noise protocol handshake.

This is a port from (Chromium's noise handshake)[https://source.chromium.org/chromium/chromium/src/+/main:third_party/cloud_authenticator/?q=third_party%2Fcloud_authenticator&ss=chromium] used for communicating with passkey enclaves.  Two excellent references for the noise protocols are:

* (The noise framework)[http://www.noiseprotocol.org/noise.html]
* (Noise explorer)[https://noiseexplorer.com/patterns/NK/]

In general, when communicating secrets to an enclave, it is recommended to use
one of the well-reviewed noise variants for multi-round communication between
clients and servers, and HPKE for launch-and-forget style requests.
