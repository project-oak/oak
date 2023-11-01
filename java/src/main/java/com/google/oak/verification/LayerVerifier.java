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
import com.google.oak.attestation.v1.TransparentReleaseEndorsement;
import com.google.oak.attestation.v1.VerifyLogEntry;
import com.google.oak.attestation.v1.VerifyLinuxKernel;
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
      r = verifyLogEntry(end.getAcpi(), ref.getAcpi());
      if (r.isPresent()) {
        return r;
      }
    } else if (endorsements.hasOakRestrictedKernel() && values.hasOakRestrictedKernel()) {
      // TBD
    } else if (endorsements.hasGenericBinary() && values.hasGenericBinary()) {
      Optional<Failure> r = verifyLogEntry(endorsements.getGenericBinary(), values.getGenericBinary());
      if (r.isPresent()) {
        return r;
      }
    } else if (endorsements.hasCborFields() && values.hasCborFields()) {
      // NYI
    }

    return Optional.of(new Failure("Mismatch in endorsenent and reference values"));
  }

  private static Optional<Failure> verifyLogEntry(TransparentReleaseEndorsement end, VerifyLogEntry ref) {
    RekorLogEntry logEntry = RekorLogEntry.createFromJson(end.getRekorLogEntry().toString());
    return LogEntryVerifier.verify(logEntry, ref.getRekorPublicKey().toByteArray(),
        end.getEndorsement().toByteArray());
  }

  private final LayerEvidence evidence;
  private final LayerEndorsements endorsements;
  Optional<Failure> initFailure;
}
