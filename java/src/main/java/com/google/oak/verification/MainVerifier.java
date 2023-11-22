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

import com.google.oak.attestation.v1.BinaryReferenceValue;
import com.google.oak.attestation.v1.ContainerLayerEndorsements;
import com.google.oak.attestation.v1.ContainerLayerReferenceValues;
import com.google.oak.attestation.v1.EndorsementReferenceValue;
import com.google.oak.attestation.v1.Endorsements;
import com.google.oak.attestation.v1.Evidence;
import com.google.oak.attestation.v1.KernelLayerEndorsements;
import com.google.oak.attestation.v1.KernelLayerReferenceValues;
import com.google.oak.attestation.v1.OakContainersEndorsements;
import com.google.oak.attestation.v1.OakContainersReferenceValues;
import com.google.oak.attestation.v1.ReferenceValues;
import com.google.oak.attestation.v1.RootLayerEndorsements;
import com.google.oak.attestation.v1.RootLayerReferenceValues;
import com.google.oak.attestation.v1.SystemLayerEndorsements;
import com.google.oak.attestation.v1.SystemLayerReferenceValues;
import com.google.oak.attestation.v1.TransparentReleaseEndorsement;
import java.util.Optional;

/** Demo implementation which assumes an Oak Container chain. */
public class MainVerifier {
  public static void main(String[] args) throws Exception {
    System.exit(2); // unimplemented
  }

  public MainVerifier(Evidence evidence) {
    this.evidence = evidence;
  }

  Optional<Failure> verifyRootLayer(
      RootLayerEndorsements endorsements, RootLayerReferenceValues values) {
    // Needs implementation
    return Optional.empty();
  }

  Optional<Failure> verifyKernelLayer(
      KernelLayerEndorsements endorsements, KernelLayerReferenceValues values) {
    // Needs implementation
    return Optional.empty();
  }

  Optional<Failure> verifySystemLayer(
      SystemLayerEndorsements endorsements, SystemLayerReferenceValues values) {
    BinaryReferenceValue systemImageValue = values.getSystemImage();
    if (systemImageValue.hasEndorsement()) {
      Optional<Failure> r =
          verifyLogEntry(endorsements.getSystemImage(), systemImageValue.getEndorsement());
      if (r.isPresent()) {
        return r;
      }
    }
    return Optional.empty();
  }

  Optional<Failure> verifyContainerLayer(
      ContainerLayerEndorsements endorsements, ContainerLayerReferenceValues values) {
    // Needs implementation
    return Optional.empty();
  }

  public Optional<Failure> verify(Endorsements endorsementsArg, ReferenceValues valuesArg) {
    if (!endorsementsArg.hasOakContainers() || !valuesArg.hasOakContainers()) {
      return Optional.of(new Failure("chain mismatch or unimplemented"));
    }

    OakContainersEndorsements endorsements = endorsementsArg.getOakContainers();
    OakContainersReferenceValues values = valuesArg.getOakContainers();

    Optional<Failure> r;
    r = verifyRootLayer(endorsements.getRootLayer(), values.getRootLayer());
    if (r.isPresent()) {
      return r;
    }
    r = verifyKernelLayer(endorsements.getKernelLayer(), values.getKernelLayer());
    if (r.isPresent()) {
      return r;
    }
    r = verifySystemLayer(endorsements.getSystemLayer(), values.getSystemLayer());
    if (r.isPresent()) {
      return r;
    }
    r = verifyContainerLayer(endorsements.getContainerLayer(), values.getContainerLayer());
    if (r.isPresent()) {
      return r;
    }

    return Optional.empty();
  }

  static Optional<Failure> verifyLogEntry(
      TransparentReleaseEndorsement end, EndorsementReferenceValue ref) {
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

  private final Evidence evidence;
}
