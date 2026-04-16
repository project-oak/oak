# Oak Session TLS

Oak Session TLS is a library for managing (optionally attested) TLS sessions
over any arbitrary reliable byte pipe. It can be used to provide TLS encryption
over abstractions besides network sockets; for example, to encapsulate a TLS
session over a bidirectional RPC stream. The primary use case for this is to
provide an end-to-end encrypted channel when it's not possible via the existing
L4 encryption mechanisms, for example, due to TLS termination in a frontend.

## Identities and Providers

The library uses `TlsIdentity` to represent the public/private key-pair that the
local node will use during the TLS handshake. It consists of DER/ASN.1 encoded
representations of the certificate and private key.

Rather than hardcoding the identity into the connection context, the library
relies on the `TlsIdentityProvider` abstraction. A `TlsIdentityProvider` is
configured on the `ServerContextConfig` (and optionally on the
`ClientContextConfig` for mutual TLS) at context creation time.

Each time a new session is instantiated from the `OakSessionTlsContext` using
`NewSession()`, the context invokes the provider's `GetIdentity()` method to
fetch the underlying `TlsIdentity`.

This abstraction allows for dynamic identity management throughout the lifetime
of the application. For instance, rather than establishing a new context, the
application can smoothly rotate its keys or refresh certificates right before
they expire.

A basic static provider is available via
`oak::session::tls::util::CreateStaticCertIdentityProvider` in C++ or
`oak_session_tls::utils::create_static_cert_identity_provider` in Rust, which
returns a provider that always yields the same `TlsIdentity` created from
explicit files or in-memory blobs. Additionally,
`CreateSelfSignedIdentityProvider` (C++) and
`create_self_signed_identity_provider` (Rust) are available to automatically
generate new self-signed certificates and keys in-memory for testing or fallback
scenarios.

## Custom Certificate Verification

In advanced scenarios, such as when enforcing attestation properties (e.g.,
DICE) or custom X.509 extensions, applications can provide extra verification
logic.

You can configure an optional `CustomCertVerifier` on the connection options
when creating a context. For C++, this is a std::function callback; for Rust, it
is a Trait implementation.

The custom verifier is called with the full certificate chain and the result of
the standard TLS validation (e.g., trust anchor verification, signature
validation, and expiry checks). This allows the custom verifier to:

1. Add additional checks after successful standard verification.
2. Override specific standard verification failures (e.g., accepting self-signed
   certificates that are not in the trust store but are verified via attestation
   evidence).

The custom verifier receives the standard verification result (as an error code
in C++, or a `Result` in Rust) and must return a status indicating whether to
accept or reject the certificate.
