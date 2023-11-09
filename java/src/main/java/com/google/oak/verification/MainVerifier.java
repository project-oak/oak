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
import com.google.oak.attestation.v1.ContainerEndorsements;
import com.google.oak.attestation.v1.ContainerReferenceValues;
import com.google.oak.attestation.v1.EndorsementReferenceValue;
import com.google.oak.attestation.v1.Endorsements;
import com.google.oak.attestation.v1.Evidence;
import com.google.oak.attestation.v1.InitEndorsements;
import com.google.oak.attestation.v1.InitReferenceValues;
import com.google.oak.attestation.v1.KernelEndorsements;
import com.google.oak.attestation.v1.KernelReferenceValues;
import com.google.oak.attestation.v1.LayerEvidence;
import com.google.oak.attestation.v1.OakContainerEndorsements;
import com.google.oak.attestation.v1.OakContainerReferenceValues;
import com.google.oak.attestation.v1.ReferenceValues;
import com.google.oak.attestation.v1.RootEndorsements;
import com.google.oak.attestation.v1.RootLayerEvidence;
import com.google.oak.attestation.v1.RootReferenceValues;
import com.google.oak.attestation.v1.TransparentReleaseEndorsement;
import java.util.ArrayList;
import java.util.List;
import java.util.ListIterator;
import java.util.Optional;
import javax.swing.text.html.Option;

/** Demo implementation which assumes an Oak Container chain. */
public class MainVerifier {
  public static void main(String[] args) throws Exception {
    System.exit(2); // unimplemented
  }

  public MainVerifier(Evidence evidence) {
    this.evidence = evidence;
  }

  Optional<Failure> verifyRootLayer(RootEndorsements endorsements, RootReferenceValues values) {
    // Needs implementation
    return Optional.empty();
  }

  Optional<Failure> verifyKernelLayer(
      KernelEndorsements endorsements, KernelReferenceValues values) {
    // Needs implementation
    return Optional.empty();
  }

  Optional<Failure> verifyInitLayer(InitEndorsements endorsements, InitReferenceValues values) {
    BinaryReferenceValue binaryValue = values.getBinary();
    if (binaryValue.hasEndorsement()) {
      Optional<Failure> r = verifyLogEntry(endorsements.getBinary(), binaryValue.getEndorsement());
      if (r.isPresent()) {
        return r;
      }
    }
    return Optional.empty();
  }

  Optional<Failure> verifyContainerLayer(
      ContainerEndorsements endorsements, ContainerReferenceValues values) {
    // Needs implementation
    return Optional.empty();
  }

  public Optional<Failure> verify(Endorsements endorsementsArg, ReferenceValues valuesArg) {
    if (!endorsementsArg.hasOakContainers() || !valuesArg.hasOakContainers()) {
      return Optional.of(new Failure("chain mismatch or unimplemented"));
    }

    OakContainerEndorsements endorsements = endorsementsArg.getOakContainers();
    OakContainerReferenceValues values = valuesArg.getOakContainers();

    Optional<Failure> r;
    r = verifyRootLayer(endorsements.getRootLayer(), values.getRootLayer());
    if (r.isPresent()) {
      return r;
    }
    r = verifyKernelLayer(endorsements.getKernelLayer(), values.getKernelLayer());
    if (r.isPresent()) {
      return r;
    }
    r = verifyInitLayer(endorsements.getInitLayer(), values.getInitLayer());
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
