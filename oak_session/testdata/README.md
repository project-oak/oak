# Oak Session Wire Format Golden Test Data

This directory contains pinned wire-format golden artifacts for `oak_session`:

- `milan_oc_release_{evidence,endorsements,reference_values}.binarypb`: Real AMD
  SEV-SNP (Milan) hardware `Evidence`, Transparent Release `Endorsements`, and
  matching `ReferenceValues` captured from an Oak Containers integration test
  run (`oak_containers_trusted_example`).
- `milan_rk_release_{evidence,endorsements,reference_values}.binarypb`: Real AMD
  SEV-SNP (Milan) hardware `Evidence`, Transparent Release `Endorsements`, and
  matching `ReferenceValues` captured from an Oak Restricted Kernel integration
  test run (`oak_echo_enclave_app`).
- `attest_{request,response}_{assertions,legacy}.binarypb`: Pinned serialized
  `oak.session.v1.SessionRequest` and `oak.session.v1.SessionResponse` wire
  messages carrying the attestation artifacts above in both bound-assertion
  (`EndorsedEvidence` and `SessionBindingKeyWrapperAssertion`) and legacy
  `endorsed_evidence` formats.
- `{bidi,uni_server,uni_client}_attestation_binding_token.bin`: Pinned
  serialized assertion binding token bytes produced during unidirectional and
  bidirectional attestation exchanges.
- `handshake_request_nn_init.binarypb` and
  `handshake_followup_assertions.binarypb`: Pinned serialized
  `oak.session.v1.SessionRequest` handshake messages (initial
  `Noise_NN_P256_AESGCM_SHA256` message and bidirectional client assertion
  binding follow-up message).
- `encrypted_{request,response}_msg0.binarypb`: Pinned serialized
  `oak.session.v1.SessionRequest` and `oak.session.v1.SessionResponse` encrypted
  transport frames produced with pinned symmetric traffic keys.

## Important

Do **not** regenerate these golden files unless you are making an **intentional,
coordinated wire-protocol change** with a backwards-compatible rollout plan for
existing deployed clients and servers.

## Regenerating Synthetic Wire Goldens

If an intentional wire-protocol change requires updating the synthetic
`.binarypb` and `.bin` wire vectors (while keeping the captured hardware
`milan_{oc,rk}_release_*` bundles unchanged), run the ignored generator test in
`oak_session/tests/wire_format_tests.rs` and copy the undeclared outputs back
into this directory:

```bash
nix develop --command bazel test //oak_session:oak_session_wire_tests \
  --test_arg=--ignored \
  --test_filter=regenerate_wire_goldens
install -m 0644 \
  bazel-testlogs/oak_session/oak_session_wire_tests/test.outputs/* \
  oak_session/testdata/
```
