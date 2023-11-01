//
// Copyright 2023 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

package com.google.oak.verification;

import com.google.oak.attestation.v1.Endorsements;
import com.google.oak.attestation.v1.Evidence;
import com.google.oak.attestation.v1.LayerEndorsements;
import com.google.oak.attestation.v1.LayerEvidence;
import com.google.oak.attestation.v1.LayerReferenceValues;
import com.google.oak.attestation.v1.ReferenceValues;
import com.google.oak.attestation.v1.RootLayerEndorsements;
import com.google.oak.attestation.v1.RootLayerEvidence;
import com.google.oak.attestation.v1.RootLayerReferenceValues;
import com.google.oak.attestation.v1.TeePlatform;
import com.google.oak.attestation.v1.TransparentReleaseEndorsement;
import com.google.oak.attestation.v1.VerifyLogEntry;
import com.google.protobuf.ByteString;
import java.lang.ref.Reference;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Optional;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class MainVerifierTest {
  private static final String LOG_ENTRY_PATH =
      "oak_remote_attestation_verification/testdata/logentry.json";
  private static final String ENDORSER_PUBLIC_KEY_PATH =
      "oak_remote_attestation_verification/testdata/oak-development.pem";
  private static final String REKOR_PUBLIC_KEY_PATH =
      "oak_remote_attestation_verification/testdata/rekor_public_key.pem";
  private static final String ENDORSEMENT_PATH =
      "oak_remote_attestation_verification/testdata/endorsement.json";

  private byte[] logEntryBytes;
  private byte[] endorserPublicKeyBytes;
  private byte[] rekorPublicKeyBytes;
  private byte[] endorsementBytes;

  @Before
  public void setUp() throws Exception {
    logEntryBytes = Files.readAllBytes(Path.of(LOG_ENTRY_PATH));
    endorserPublicKeyBytes =
        SignatureVerifier.convertPemToRaw(Files.readString(Path.of(ENDORSER_PUBLIC_KEY_PATH)));
    rekorPublicKeyBytes =
        SignatureVerifier.convertPemToRaw(Files.readString(Path.of(REKOR_PUBLIC_KEY_PATH)));
    endorsementBytes = Files.readAllBytes(Path.of(ENDORSEMENT_PATH));
  }

  private TransparentReleaseEndorsement createTREndorsement() {
    ByteString endorsement = ByteString.copyFrom(endorsementBytes);
    ByteString logEntry = ByteString.copyFrom(logEntryBytes);
    return TransparentReleaseEndorsement.newBuilder()
        .setEndorsement(endorsement)
        .setRekorLogEntry(logEntry)
        .build();
  }

  private static Evidence createEvidence() {
    return Evidence.newBuilder()
        .setRootLayer(RootLayerEvidence.newBuilder()
                          .setPlatform(TeePlatform.AMD_SEV_SNP)
                          .setRemoteAttestationReport(ByteString.copyFromUtf8("whatever")))
        .addLayers(
            LayerEvidence.newBuilder().setEcaCertificate(ByteString.copyFromUtf8("whatever")))
        .build();
  }

  private Endorsements createEndorsements() {
    return Endorsements.newBuilder()
        .setRootLayer(
            RootLayerEndorsements.newBuilder().setStage0Endorsement(createTREndorsement()))
        .addLayers(LayerEndorsements.newBuilder().setGenericBinary(createTREndorsement()))
        .build();
  }

  private ReferenceValues createReferenceValues() {
    ByteString endorserPublicKey = ByteString.copyFrom(endorserPublicKeyBytes);
    ByteString rekorPublicKey = ByteString.copyFrom(rekorPublicKeyBytes);

    return ReferenceValues.newBuilder()
        .setRootLayer(RootLayerReferenceValues.newBuilder())
        .addLayers(LayerReferenceValues.newBuilder().setGenericBinary(
            VerifyLogEntry.newBuilder()
                .setEndorserPublicKey(endorserPublicKey)
                .setRekorPublicKey(rekorPublicKey)))
        .build();
  }

  @Test
  public void testVerifySucceeds() {
    Evidence evidence = createEvidence();
    Endorsements endorsements = createEndorsements();
    ReferenceValues referenceValues = createReferenceValues();

    MainVerifier verifier = new MainVerifier(evidence, endorsements);
    Optional<Failure> failure = verifier.verify(referenceValues);

    if (failure.isPresent()) {
      System.out.println(failure.get().getMessage());
    }
    Assert.assertFalse(failure.isPresent());
  }
}
