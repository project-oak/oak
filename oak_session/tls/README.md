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

## Server Name and SAN Verification

By default, the library uses `"oak-session-tls"` as the server identity for both
SNI (Server Name Indication) and certificate SAN (Subject Alternative Name)
verification. This name is embedded in self-signed certificates and verified by
the client during the TLS handshake.

To use a custom server identity, set `expected_server_name` on the
`ClientContextConfig`:

```rust
// Rust
let config = ClientContextConfig {
    expected_server_name: Some("my-service.example.com".to_string()),
    ..
};
```

```cpp
// C++
ClientContextConfig config{
    .expected_server_name = "my-service.example.com",
};
```

When using self-signed certificates, the server must generate its certificate
with a matching SAN:

```rust
// Rust
let provider = utils::create_self_signed_for("my-service.example.com")?;
```

```cpp
// C++
auto provider = util::CreateSelfSigned("my-service.example.com");
```

If `expected_server_name` is not set, it defaults to `"oak-session-tls"`,
preserving backward compatibility with existing deployments.

**Interaction with custom verifiers:** The SAN check is part of standard
WebPKI/X.509 verification. A `CustomCertVerifier` receives the result of
standard verification (including any SAN mismatch) and can choose to override
failures or add additional checks.

## Handshake and Initial Application Data (`initial_data`)

When completing the TLS handshake via `new_initialized_session` (Rust) or
`NewInitializedSession` (C++), the initializer returns both the established
session object and a buffer of `initial_data` (as a `Vec<u8>` in Rust or
`std::string` in C++).

### What is `initial_data`?

During the TLS 1.3 handshake, the client may bundle its first application-level
request payload with the final handshake message (like the `Finished` message)
in a single TCP or transport flight. When the server processes this flight to
complete the TLS handshake, the underlying TLS library (rustls or BoringSSL)
decrypts this trailing application data and places it into its internal read
buffer.

The initializer drains this buffer before returning, exposing it as
`initial_data`.

### Handling `initial_data` Correctly

1. **Check and Process:** The caller MUST check if `initial_data` is non-empty.
   If it contains data, the application must process it as the first incoming
   message.
2. **Do Not Expect Full Messages:** `initial_data` contains raw decrypted bytes
   received from the transport. It is **not** guaranteed to represent a
   complete, deserializable message or a full protobuf. Its contents and framing
   depend entirely on the application-level protocol.
   - For example, in a gRPC-over-TLS stream, `initial_data` might contain only a
     partial gRPC frame, or a gRPC frame header followed by the serialized
     request protobuf.
   - In stream-based protocols, it may contain only a fragment of a larger
     message.
3. **Feed to the Framing Layer:** The caller should buffer these bytes or feed
   them directly to the application's message framing/deserialization layer,
   exactly as if they had been read from the stream after the handshake.
4. **Subsequent Decryptions:** Because these bytes have already been decrypted
   and drained from the TLS buffer during the handshake, calling `decrypt`
   (Rust) or `Decrypt` (C++) on newly received transport frames will **not**
   yield this data again. If you ignore `initial_data` and wait for the next
   transport frame, the application may hang or lose the initial request.
