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

import com.google.oak.RawDigest;
import com.google.oak.attestation.v1.LayerEvidence;
import com.google.oak.attestation.v1.CustomLayerReferenceValues;
import com.google.oak.attestation.v1.CustomLayerEndorsements;
import com.google.oak.attestation.v1.TransparentReleaseEndorsement;
import com.google.oak.attestation.v1.LogEntryVerification;
import java.util.List;
import java.util.Map;
import java.util.Optional;

class LayerVerifier {
  public LayerVerifier(LayerEvidence evidence, CustomLayerEndorsements endorsements) {
    this.evidence = evidence;
    this.endorsements = endorsements;
  }

  public Optional<Failure> verify(CustomLayerReferenceValues values) {
    if (endorsements.hasBinary() && values.hasLogEntry()) {
      return verifyLogEntry(endorsements.getBinary(), values.getLogEntry());
    }

    return Optional.of(new Failure("Mismatch in endorsement and reference values"));
  }

  static Optional<Failure> verifyLogEntry(
      TransparentReleaseEndorsement end, LogEntryVerification ref) {
    RekorLogEntry logEntry;
    try {
      logEntry = RekorLogEntry.createFromJson(end.getRekorLogEntry().toStringUtf8());
    } catch (IllegalArgumentException e) {
      return Optional.of(
          new Failure(String.format("%s: %s", e.getClass().getName(), e.getMessage())));
    }
    return LogEntryVerifier.verify(
        logEntry, ref.getRekorPublicKey().toByteArray(), end.getEndorsement().toByteArray());
  }

  private final LayerEvidence evidence;
  private final CustomLayerEndorsements endorsements;
  Optional<Failure> initFailure;
}
