# Oak Attestation Integration Tests

This crate provides comprehensive integration tests and utilities for Oak's
attestation system. It serves three main purposes:

1. **Attestation Output Analysis**:
   - A binary utility that analyzes attestation output for breaking changes.
   - It saves new snapshots when the output changes.
   - Snapshots are ordered starting at 00000, progressing to 00001 and so on.
   - This utility must be run and its output committed whenever changes are made
     that alter attestation output.

2. **Verification Backwards Compatibility Checks**:
   - Tests the current verification library against snapshots of past
     attestation outputs, ensuring that verification succeeds.

3. **Attestation Integration Testing**:
   - Tests covering the full workflow from generating an attestation to
     verifying it.

## CI Failure Guide

If you encounter a CI failure related to this crate, it likely means one of four
things (from most to least likely):

1. **Attestation Output Snapshot Update Required**:
   - You've made changes that alter the attestation output, but haven't created
     a snapshot.
   - Action: Run `update_testdata_assert_no_breaking_changes` locally, commit
     the new snapshot, and push your changes.

2. **Breaking Changes in Attestation Output Detected**:
   - The attestation output has changed in a way that could break verification
     for older versions.
   - Action: Reimplement the change in a non breaking way. Changes should be
     additive. Implement them by adding new fields, not by altering or deleting
     current ones. Consult with the team if assistance needed.

3. **Breaking Changes in Verification Library Detected**:
   - The verification library has been modified in a way that older evidence in
     snapshot no longer verifies.
   - Action: This is a serious issue that requires careful consideration. Review
     the breaking changes to ensure they are necessary. Usually it's possible to
     implement changes in a way that maintains compatability with verifying old
     version of evidence. If that is not possible, consult with the team to
     determine the best course of action.

4. **Current Attestation-Verification Pairing Failure**:
   - The integration tests pairing the current attestation logic with the
     current verification logic are failing.
   - Action: This indicates a mismatch between the current attestation output
     and what the verification process expects. Debug the changes in both the
     attestation and verification components to identify the source of the
     discrepancy.

## Future Work and Considerations

1. **Snapshot Versioning**:
   - Currently, snapshots are incrementally numbered (000000, 000001, etc.).
   - This approach simplifies identifying the latest snapshot but may lead to
     merge conflicts if multiple changes occur simultaneously.
   - Future consideration: Implement a more robust versioning system that
     reduces the likelihood of conflicts.

2. **Snapshot Retention Policy**:
   - Snapshots should realistically represent the distribution of evidence "in
     the wild", potentially with a conservative approach.
   - We should establish a policy for deleting old snapshots based on the
     phasing out of the logic that generated them.
   - Deletion criteria:
     - 100% certainty that the logic generating a snapshot has been phased out.
     - Or, ~99% phased out with acceptance of breaking the remaining 1% of
       clients.
   - This approach ensures that our test suite remains relevant to real-world
     scenarios while allowing for careful pruning of outdated evidence.
   - TODO: b/372045744 - Develop a mechanism to track the lifecycle of
     evidence-generating logic and implement a process for safe snapshot
     deletion.

3. **Breaking Changes to Attestation Outputs**:
   - In the future, we may need to allow breaking changes (e.g., removing
     fields) to attestation outputs.
   - This would be based on the assumption that no clients in production are
     still using old versions of the verification library that read these
     fields.
   - Challenges:
     - Our current testing doesn't verify against old client versions.
     - We only check that old fields remain set, without knowledge of their
       continued relevance.
   - Future work:
     - Develop a strategy for safely implementing breaking changes.
     - Consider implementing a deprecation period for fields before removal.
     - Explore ways to test compatibility with older client versions or maintain
       a registry of field usage.

## Crate Organization

This crate is separate from individual attestation/verification components due
to its dependencies. It relies on a mix of crates, some of which are not
available in google3.

For tests specific to individual aspects of attestation/verification that don't
have external dependencies, place them in the relevant component crate. This
ensures they can run in google3 if the crate is imported.
