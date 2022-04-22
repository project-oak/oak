# Offline Attestation

The current Oak Functions Runtime implementation uses an interactive handshake
for setting up an attested end-to-end encrypted channel between the client and
the runtime. For some scenarios it might be preferable to avoid the handshake.

The offline attestation approach splits the attestation process into two
distinct parts:

- Key generation and export: A single asymmetric key-pair is generated. The
  public key is bound to an attestation report that provides evidence about the
  enclave that generated the private key. The public key and attestation report
  are then made availble to clients.
- Encrypted communications: Clients use the public key (once they are satisfied
  by the evidence that only appropriate enclaves would have access to the
  private key) to encrypt requests to the server. Clients also provide
  additional information (e.g. the client's public key) in the request to allow
  the server to encrypt the response.

- This approach has some advantages compared to the interactive handshake-based
  approach:
  - Reduced bandwith and latency
  - No need for sticky sessions in a load-balanced environment
- And some disadvantages:
  - No forward secrecy since the same public key is used for encrypting all
    requests
  - No built-in replay protection

## Implementation Details

This experimental example provides simplified client and server implementations.

### Server

The server generates an asymmetric key-pair at startup. It then generates an
attestation report that binds the public key to the enclave hardware and the
version of the server code. For this example we just generate a fake empty
attestation report that is always accepted by the client.

For more realistic implementations that support load-balancing a
key-provisioning mechanism is required to ensure that all instances of the
server have access to the private key. This could be done in two ways:

- A separate key management server (KMS): The KMS would generate the key-pair
  and attestation report. When a server instance starts up it sets up a
  mutually-attested connection with the KMS and requests the private key. The
  KMS is then responsible for validating that the server is running an
  appropriate version of the software in an appropriate enclave before sharing
  the private key. The attestation report will include evidence about the KMS,
  not the server, so the KMS code would need to be reviewed to ensure that it
  will do the server validation correctly.
- Key-sharing between servers: The first server to start up will be instructed
  to generate a key-pair and attestation reports. When other servers start up,
  they will be instructed to connect to an existing server to get the private
  key via a mutually-attested connection. This approach might present some
  challenges for key rotation or upgrading to new versions of the server code.

Once the server has access to the private key it can start serving requests. It
decrypts the ciphertext from each request. The request also includes a public
key for the client. The server processes the cleartext, encrypts it with the
client's public key, and returns the encrypted response.

### Client

For illustration purposes the client fetches the public key and associated
attestation report from the server and validates the report. In a more realistic
implemenation the retrieval and validation of the public key and attestation
report would happen out-of-band. The public key would then be provided to the
client app once the validity of the key and attestation report has been
confirmed. This could be done through client configuration, or embedding the key
into the client code.

This example uses an empty fake attestation report that is always assumed to be
valid. In a realistic implementation the attestation report would be generated
by the enclave hardware and include the hash of the public key. The report would
also include a measurement of the code running in the enclave. Validating the
report should include checks to ensure that the code would treat the decrypted
data appropriately and not leak the private key from the enclave.

Once the client has the server's public key it encrypts the request. The client
also generates its own asymmetric key-pair and includes the public key in the
request. This provides a mechansim for the server to encrypt the response back
to the client.

When the client receives the encrypted response from the server it decrypts it
using is private key and processes the cleartext content.

### Hybrid Encryption

This example uses Tink's implementation of
[ECIES hybrid encryption](https://github.com/project-oak/tink-rust/tree/main/hybrid):

- Key agreement: ECDH using the NIST P-256 curve
- Key derivation: HKDF using SHA256 with an empty salt
- Authenticated encryption: 128-bit AES_GCM

## Running the Example

Start an instance of the server:

```bash
RUST_LOG=debug cargo run \
    --manifest-path=experimental/offline_attestation/server/Cargo.toml
```

In another terminal, run the client while the server is running:

```bash
RUST_LOG=debug cargo run \
    --manifest-path=experimental/offline_attestation/client/Cargo.toml
```
