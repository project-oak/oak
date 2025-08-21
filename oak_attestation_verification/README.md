<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="oak-logo/svgs/oak-logo-negative.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="oak-logo/svgs/oak-logo.svg?sanitize=true"><img alt="Project Oak Logo" src="oak-logo/svgs/oak-logo.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Oak Attestation Verification SDK

This library provides the tools to validate the authenticity and integrity of a
workload running in a Trusted Execution Environment (TEE) by verifying remote
attestation artifacts such as [`Evidence`](../proto/attestation/evidence.proto)
and [`Endorsements`](../proto/attestation/endorsement.proto).

## Attestation Verifier

The main entry point for this library is the `AttestationVerifier` trait, which
provides a standard interface for attestation verification.

```rust
pub trait AttestationVerifier {
    fn verify(
        &self,
        evidence: &Evidence,
        endorsements: &Endorsements,
    ) -> anyhow::Result<AttestationResults>;
}
```

Oak provides several implementations of this trait:

- `AmdSevSnpDiceAttestationVerifier`: that verifies the
  [AMD SEV-SNP](https://www.amd.com/en/developer/sev.html) attestation report
  and also verifies the validity of the [DICE](../docs/remote-attestation.md)
  chain.
- `EventLogVerifier`: a special verifier that only validates that the values in
  the event log entries match the expected values (reference values or
  endorsements). Note: it doesn't check that the event log is rooted in hardware
  attestation _(needed for use-cases where the evidence is produced by a trusted
  party outside of the TEE)_.

The final result of the attestation verification is an
[`AttestationResults`](../proto/attestation/verification.proto) message, which
indicates success or failure and also includes various artifacts extracted from
the evidence _(such as public keys associated with the workload)_.

## Verification Policies

On the lower level attestation verification is implemented by Verification
Policies (also called _"Appraisal Policies"_ in
[RFC9334](https://datatracker.ietf.org/doc/html/rfc9334#name-appraisal-policies)).

A Verification Policy is a function that can validate the authenticity and
integrity of an individual event provided by the `Evidence`. Here we consider
both "events" from the [`EventLog`](../proto/attestation/eventlog.proto) and
also "special events" such as Platform event (i.e. containing an AMD SEV-SNP
attestation report) and Firmware event (i.e. containing measurements for
[stage0](../stage0_bin/README.md)). In addition to verifying an event,
Verification Policy also needs to verify that this Event is endorsed. This means
that each event from the `Evidence` needs to have a corresponding event
endorsement in the `Endorsements`. These event endorsements are represented by
the `platform`, `initial` (firmware) and the `events` fields of the
`Endorsements` message.

Verification policy is represented as a `Policy` trait:

```rust
pub trait Policy<T> {
    fn verify(
        &self,
        event: &T,
        endorsement: &Variant,
        now_utc_millis: i64,
    ) -> anyhow::Result<EventAttestationResults>;
}
```

Additional argument that is provided to policies is `now_utc_millis`, which
corresponds to the current time and is used to check certificate validity (e.g.
for [Transparent Release](../docs/tr/README.md)).

Each event type requires having an individual implementation of the policy trait
that can verify such an event. For example, the Kernel Event, that corresponds
to loading and measuring the kernel, requires a
[`KernelPolicy`](src/policy/kernel.rs). Oak attestation verification library
provides a set of [default policies](src/policy/), which can be initialized with
reference values that these policies will use to validate the event and the
event endorsement.

Verification policies are also used to create instances of the
`AttestationVerifier` (e.g. `AmdSevSnpDiceAttestationVerifier`), which the
verifier uses internally by iterating over the provided events and calling
respective verification policies. Keep in mind that the implementation
`AttestationVerifier` still needs to validate that those events are rooted in
the attestation report, which is not done by policies and instead uses other
mechanisms internal to the `AttestationVerifier` implementation (such as
[DICE](https://trustedcomputinggroup.org/work-groups/dice-architectures/)
mechanism).

## Example

This example shows how to perform attestation verification for
[Oak Containers](../oak_containers/README.md):

```rust
use anyhow::Context;
use oak_attestation_verification::{
    policy::{
        container::ContainerPolicy, firmware::FirmwarePolicy, kernel::KernelPolicy,
        platform::AmdSevSnpPolicy, system::SystemPolicy,
    },
    verifier::AmdSevSnpDiceAttestationVerifier,
};
use oak_attestation_verification_types::{
    policy::Policy, util::Clock, verifier::AttestationVerifier,
};
use oak_proto_rust::oak::attestation::v1::{
    AttestationResults, Endorsements, Evidence, OakContainersReferenceValues,
};

fn verify(
    evidence: &Evidence,
    endorsements: &Endorsements,
    ref_vals: &OakContainersReferenceValues,
) -> anyhow::Result<AttestationResults> {
    // Create platform and firmware policies.
    let root_layer_ref_vals =
        ref_vals.root_layer.as_ref().context("no root reference value provided")?;
    let platform_policy = AmdSevSnpPolicy::from_root_layer_reference_values(root_layer_ref_vals)?;
    let firmware_policy = FirmwarePolicy::from_root_layer_reference_values(root_layer_ref_vals)?;

    // Create kernel policy.
    let kernel_ref_vals =
        ref_vals.kernel_layer.as_ref().context("no kernel reference value provided")?;
    let kernel_policy = KernelPolicy::new(kernel_ref_vals);

    // Create system policy.
    let system_ref_vals =
        ref_vals.system_layer.as_ref().context("no system reference value provided")?;
    let system_policy = SystemPolicy::new(system_ref_vals);

    // Create container policy.
    let container_ref_vals =
        ref_vals.container_layer.as_ref().context("no container reference value provided")?;
    let container_policy = ContainerPolicy::new(container_ref_vals);

    let event_policies: Vec<Box<dyn Policy<[u8]>>> =
        vec![Box::new(kernel_policy), Box::new(system_policy), Box::new(container_policy)];

    // Create verifier.
    let verifier = AmdSevSnpDiceAttestationVerifier::new(
        platform_policy,
        Box::new(firmware_policy),
        event_policies,
        // Clock should implement the `Clock` trait: `oak_attestation_types::util::Clock`.
        Arc::new(SystemClock {}),
    );

    // Perform attestation verification.
    verifier.verify(evidence, endorsements)
}
```
