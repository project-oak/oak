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

import com.google.oak.attestation.v1.Evidence;
import com.google.oak.attestation.v1.Endorsements;
import com.google.oak.attestation.v1.LayerEndorsements;
import com.google.oak.attestation.v1.LayerEvidence;
import com.google.oak.attestation.v1.LayerReferenceValues;
import com.google.oak.attestation.v1.ReferenceValues;
import com.google.oak.attestation.v1.RootLayerEvidence;
import com.google.oak.attestation.v1.RootReferenceValues;
import java.util.Optional;

import javax.swing.text.html.Option;

import java.util.ArrayList;
import java.util.List;
import java.util.ListIterator;

public class MainVerifier {
  public static void main(String[] args) throws Exception {
    System.exit(2); // unimplemented
  }

  public MainVerifier(Evidence evidence, Endorsements endorsements) {
    this.evidence = evidence;
    this.endorsements = endorsements;
    if (evidence.getLayersCount() == endorsements.getLayersCount()) {
      this.initFailure = Optional.empty();
      int layerCount = evidence.getLayersCount();
      for (int i = 0; i < layerCount; ++i) {
        layerVerifiers.add(new LayerVerifier(evidence.getLayers(i), endorsements.getLayers(i)));
      }
    } else {
      this.initFailure = Optional.of(new Failure("Layer count mismatch"));
    }
  }

  public Optional<Failure> getInitFailure() {
    return initFailure;
  }

  public Optional<Failure> verifyRoot(RootReferenceValues values) {
    // Needs implementation
    return Optional.empty();
  }

  public Optional<Failure> verify(ReferenceValues values) {
    if (initFailure.isPresent()) {
      return initFailure;
    }

    Optional<Failure> r = verifyRoot(values.getRootLayer());
    if (r.isPresent()) {
      return r;
    }
    ListIterator<LayerVerifier> it = layerVerifiers.listIterator();
    while (it.hasNext()) {
      r = it.next().verify(values.getLayers(it.nextIndex()));
      if (r.isPresent()) {
        return r;
      }
    }

    return Optional.empty();
  }

  private final Evidence evidence;
  private final Endorsements endorsements;
  Optional<Failure> initFailure;
  private final List<LayerVerifier> layerVerifiers = new ArrayList<>();
}
