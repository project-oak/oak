#!/bin/bash
#
# Simple integration test which invokes the CLI against actual storage and
# checks process return code.
#
# Invoke by:
#     bazel test tr/endorscope_cli:tests
#
# When listing without a fixed timestamp, we restrict the number of listed
# items to a few and assume that they verify correctly with respect to the
# current time because new endorsements are continuously generated.
#
# As long as nothing is removed from the oak-files, oak-index bucket pair,
# these tests should pass. If they get cleaned up at some point, then some]
# hashes below need to be updated.
#
set -e

readonly TESTDATA_DIR=oak_attestation_verification/testdata

# oak_functions_insecure_container
${CLI} list \
  --fbucket=oak-files --ibucket=oak-index \
  --endorser-keyset-hash=sha2-256:187c592ed901e281d5bc55a5b9323f2c2cd857d78d8e8c4141b20890b823e84a \
  --limit=2

echo "===== 👍👍👍 listing by endorser keyset works ======================="

# oak_functions_insecure_container
${CLI} list \
  --fbucket=oak-files --ibucket=oak-index \
  --endorser-key-hash=sha2-256:ee037d0a0086a8f66f292832cdf0fc1e664b8ddf339404b8001ab4ac4509ca7a \
  --limit=2

echo "===== 👍👍👍 listing by endorser key works =========================="

# Replicated ledger. The same binary is released repeatedly, therefore need
# to limit. Verification time: 7 October 2025, 18:00 UTC.
# TBD: Test might break in the future, need to bump the timestamp.
${CLI} --now-utc-millis=1759860000000 list \
  --fbucket=oak-files --ibucket=oak-index \
  --subject-hash=sha2-256:4e0acdea53c7004a03395317509a29b1a743719e02120a3a5af6f47505a1e14a \
  --limit=1

echo "===== 👍👍👍 listing by subject works ==============================="

# That key_xor_test_app was released once, and is also on staging.
# Verification time: 8 October 2025, 18:00 UTC.
# TBD: Test might break in the future, need to bump the timestamp.
${CLI} --now-utc-millis=1759946400000 list \
  --fbucket=oak-files --ibucket=oak-index \
  --subject-hash=sha2-256:5902ee447d003a2f331d1a91520c92a15571e76b8b8b1b8124fe88a25f4374f3 \
  --rekor-public-key= \
  --limit=2

echo "===== 👍👍👍 listing by subject (no log entry) works ================"

# Verification time: 7 October 2025, 18:00 UTC.
${CLI} --now-utc-millis=1759860000000 verify remote \
  --fbucket=oak-files --ibucket=oak-index \
  --endorsement-hash=sha2-256:eb8150f44a8e583a7f9e829d8855644b440c41d8ccc71df7a66002f6c0ca3a93

echo "===== 👍👍👍 verifying remotely works ==============================="

# Staging endorsement of key_xor_test_app.
# Verification time: 7 October 2025, 18:00 UTC.
${CLI} --now-utc-millis=1759860000000 verify remote \
  --fbucket=oak-files --ibucket=oak-index \
  --endorsement-hash=sha2-256:55852ee65033ef159a39be007b4d56a9da9bf0e0119abedc3687549a5da879df \
  --rekor-public-key=

echo "===== 👍👍👍 verifying remotely (without log entry) works ==========="

# Verification time: 1 March 2024, 1:00 UTC.
${CLI} --now-utc-millis=1709254800000 verify file \
  "--endorsement=${TESTDATA_DIR}/endorsement.json" \
  "--signature=${TESTDATA_DIR}/endorsement.json.sig" \
  "--log-entry=${TESTDATA_DIR}/logentry.json" \
  "--endorser-public-key=${TESTDATA_DIR}/endorser_public_key.pem"

echo "===== 👍👍👍 verifying file works ==================================="
