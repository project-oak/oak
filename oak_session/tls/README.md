# Oak Session TLS

Oak Session TLS is a library for managing (optionally attested) TLS sessions
over any arbitrary reliable byte pipe. It can be used to provide TLS encryption
over abstractions besides network sockets; for example, to encapsulate a TLS
session over a bidirectional RPC stream. The primary use case for this is to
provide an end-to-end encrypted channel when it's not possible via the existing
L4 encryption mechanisms, for example, due to TLS termination in a frontend.
