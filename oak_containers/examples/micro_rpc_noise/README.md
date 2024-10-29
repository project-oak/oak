# microRPC Standalone Example

This directory shows a completely stand-alone example of an Oak Application that
uses microRPC as the service communication layer, and uses the Noise Protocol to
handle encryption.

- `application` contains the actual application business logic that the rest of
  the demo exposes.
- `proto` contains the proto messages and service defintions
- `service` contains the implementation of the microRPC service
- `tests` shows a simple end-to-end example

Since microRPC currently only supports unary requests, we use the lifetime of of
the TrustedApplicationService to define the lifetime bounds.
