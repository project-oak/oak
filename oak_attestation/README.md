<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="oak-logo/svgs/oak-logo-negative.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="oak-logo/svgs/oak-logo.svg?sanitize=true"><img alt="Project Oak Logo" src="oak-logo/svgs/oak-logo.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Oak Attestation SDK

This library provides an implementation of the
[`Attester`](../oak_attestation_types/src/attester.rs), which abstracts away the
underlying details of the TEE platform (e.g.,
[AMD SEV-SNP](https://www.amd.com/en/developer/sev.html) or
[Intel TDX](https://www.intel.com/content/www/us/en/developer/tools/trust-domain-extensions/overview.html))
and provides a unified inferface for generating the
[`Evidence`](../proto/attestation/evidence.proto) message needed for
[Remote Attestation](../docs/remote-attestation.md).

## Event Log

The Attester utilises the notion of "Event Log" to build the Evidence piece by
piece. The Event Log was introduced to create a platform-agnostic format for
storing detailed software measurements. Each
[`Event`](../proto/attestation/eventlog.proto) in the log can represent a change
of state in the workload, such as loading a new software component into the
Trusted Computing Base (TCB) or generating cryptographic keys. This concept is
inspired by the measurement model used in
[Intel TDX](https://www.intel.com/content/www/us/en/developer/tools/trust-domain-extensions/overview.html).

## Attester

Attester is represented as the following trait (defined in
[`oak_attestation_types`](../oak_attestation_types/src/attester.rs)):

```rust
pub trait Attester {
    fn extend(&mut self, encoded_event: &[u8]) -> Result<()>;
    fn quote(&self) -> Result<Evidence>;
}
```

- `extend` function accepts an `encoded_event` (which is a serialized
  [`Event`](../proto/attestation/eventlog.proto) message) and adds it to the
  internal `EventLog` representation.
- `quote` function generates the final `Evidence` message containing a record of
  all the previously added events.

Attester collects events in the
[`EventLog`](../proto/attestation/eventlog.proto) message, which is embedded in
the [`Evidence`](../proto/attestation/evidence.proto). An `Event` contains a
specific event type in the `event` field as a `google.protobuf.Any`. Each
`Event` message is serialized and placed in the `encoded_events` field of the
Event Log. Examples of various events supported by Oak can be found here:
[`verification.proto`](../proto/attestation/verification.proto).

It's important to note that the integrity of the event log must be enforced by
hardware, i.e. the event log must be rooted in the attestation report, which
depends on the exact implementation (SNP or TDX).

### Transparent Attester

Transparent Attester is represented as the following trait (defined in
[`oak_attestation_types`](../oak_attestation_types/src/transparent_attester.rs))
and may be used in conjunction with the original Attester trait:

```rust
pub trait TransparentAttester {
    fn extend_transparent(&mut self, original_encoded_event: &[u8], transparent_encoded_event: &[u8]) -> Result<()>;
}
```

- `extend_transparent` function accepts an `original_encoded_event` and a
  `transparent_encoded_event`. The `original_encoded_event` contains potentially
  sensitive data. The `transparent_encoded_event` is a version of the same
  encoded event that does not contain sensitive data (for example, sensitive
  entries in the `original_encoded_event` are hashed). Both of these encoded
  events are serialized [`Event`](../proto/attestation/eventlog.proto) messages.
  and adds it to the internal `EventLog` representation.

Transparent Attester collects events across two
[`EventLog`](../proto/attestation/eventlog.proto) messages. These event logs are
embedded in the [`Evidence`](../proto/attestation/evidence.proto).

If implementing this trait, it must be implemented along with the original
Attester trait because this trait does not provide a `quote` function for the
final `Evidence` message.

## DICE

One of the Attester implementations provided by the Oak SDK is
[`DiceAttester`](../oak_attestation/src/dice.rs), which is based on the
[Device Identifier Composition Engine (DICE)](https://trustedcomputinggroup.org/work-groups/dice-architectures/)
model.

DICE provides a mechanism for combining software measurements and corresponding
certificates into a chain, where each element (called a "layer") often
represents a software component (or multiple) loaded into the VMs memory. These
layers are loaded sequentially (e.g., firmware loads the kernel, the kernel
loads the application), and the previous layer is responsible for measuring the
next layer. Each layer is provided with a private key (called the _Certificate
Authority Key_) by the previous layer, which it can use to sign the measurement
of the next layer, thus contributing to the DICE certificate chain. In our
implementation each DICE layer corresponds to an event from the event log, which
means that layer measurements are stored in `Event` messages.

DICE mechanism is represented in the `Evidence` as the following messages:

- `RootLayerEvidence`: Message that contains hardware remote attestation report
  and a measurement of the firmware (i.e. [`stage0`](../stage0_bin/README.md)).

  - Note: Strictly speaking it's not a DICE layer, it's just a message just
    binds the root public key into the hardware-based attestation

- `repeated LayerEvidence`: Messages representing DICE layers.

DICE layers are linked together into a certificate chain using the following
mechanism:

1. When the TEE starts, the VMM loads the firmware and the platform (e.g. AMD
   Secure Processor) into the memory and measures the initial memory layout
   before starting the firmware.

1. When the firmware starts, it generates a Certificate Authority Keypair
   `(S_0, P_0)` for itself and requests the TEE hardware to sign the hash of the
   public key `P_0`.

   - TEE generates a signed attestation report that contains the measurement of
     the initial memory layout and the the public key `P_0` hash.
   - Attestation report is stored in the `RootLayerEvidence`.
   - Firmware is considered a _Layer0_ (or _Root Layer_).

1. Firmware loads the next layer (typically the
   [kernel](../oak_restricted_kernel_bin/README.md)) into the memory and
   measures it.

1. Firmware then generates a new key pair `(S_1, P_1)` intended for the next
   layer, and uses its own private key `S_0` to issue a signed
   [CBOR Web Token (CWT)](https://www.rfc-editor.org/rfc/rfc8392.html)
   containing the measurement of the next layer and its public key `P_1` hash.

   - Next layer's measurement is stored in a new `Event` message and the CWT
     contains the hash of the serialized `Event` as a _"claim"_.
   - CWT is signed using the `S_0` key.
   - Corresponding serialized `Event` message is also stored in the `EventLog`.
   - CWT is stored in the `LayerEvidence` field corresponding to the _Layer1_.

1. Firmware starts the next layer and gives it access to the Certificate
   Authority Keypair `(S_1, P_1)` and to the current version of the `Evidence`
   message (so that it could be extended by the next layer).

   - This is done by serializing the `DiceAttester` and sending it to the next
     layer as a [`DiceData`](../proto/attestation/dice.proto) message.
   - It's important to note that each layer must delete its own private key
     before starting the next layer. If the next layer gets access to the
     private key of the previous layer it could rewrite the DICE chain.

1. The process continues by each following _Layer(K-1)_, who generates a key
   pair `(S_K, P_K)`, measures the next layer and creates a new CWT using the
   key `S_(K-1)`.
