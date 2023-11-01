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

import com.google.oak.attestation.v1.LayerEvidence;
import com.google.oak.attestation.v1.LayerEndorsements;
import com.google.oak.attestation.v1.LayerReferenceValues;
import com.google.oak.attestation.v1.LinuxKernelEndorsement;
import com.google.oak.attestation.v1.Measurements;
import com.google.oak.attestation.v1.TransparentReleaseEndorsement;
import com.google.oak.attestation.v1.VerifyLogEntry;
import com.google.oak.attestation.v1.VerifyLinuxKernel;
import com.google.oak.RawDigest;
import java.util.List;
import java.util.Map;
import java.util.Optional;

class LayerVerifier {
  public LayerVerifier(LayerEvidence evidence, LayerEndorsements endorsements) {
    this.evidence = evidence;
    this.endorsements = endorsements;
  }

  public Optional<Failure> verify(LayerReferenceValues values) {
    if (endorsements.hasLinuxKernel() && values.hasLinuxKernel()) {
      LinuxKernelEndorsement end = endorsements.getLinuxKernel();
      VerifyLinuxKernel ref = values.getLinuxKernel();
      Optional<Failure> r = verifyLogEntry(end.getKernelBinary(), ref.getKernelBinary());
      if (r.isPresent()) {
        return r;
      }
      r = verifyLogEntry(end.getKernelCmdLine(), ref.getKernelCmdLine());
      if (r.isPresent()) {
        return r;
      }
      return verifyLogEntry(end.getAcpi(), ref.getAcpi());
    } else if (endorsements.hasOakRestrictedKernel() && values.hasOakRestrictedKernel()) {
      return Optional.of(new Failure("Not yet implemented"));
    } else if (endorsements.hasGenericBinary() && values.hasGenericBinary()) {
      return verifyLogEntry(endorsements.getGenericBinary(), values.getGenericBinary());
    } else if (values.hasCborFields()) {
      return Optional.of(new Failure("Not yet implemented"));
    }

    return Optional.of(new Failure("Mismatch in endorsement and reference values"));
  }

  private static Optional<Failure> verifyLogEntry(TransparentReleaseEndorsement end, VerifyLogEntry ref) {
    RekorLogEntry logEntry;
    try {
      logEntry = RekorLogEntry.createFromJson(end.getRekorLogEntry().toStringUtf8());
    } catch (IllegalArgumentException e) {
      return Optional.of(new Failure(String.format("%s: %s", e.getClass().getName(), e.getMessage())));
    }
    return LogEntryVerifier.verify(
        logEntry, ref.getRekorPublicKey().toByteArray(), end.getEndorsement().toByteArray());
  }

  private final LayerEvidence evidence;
  private final LayerEndorsements endorsements;
  Optional<Failure> initFailure;
}
