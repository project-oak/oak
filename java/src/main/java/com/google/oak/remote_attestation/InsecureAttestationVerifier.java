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

package com.google.oak.remote_attestation;

import co.nstant.in.cbor.CborBuilder;
import co.nstant.in.cbor.CborDecoder;
import co.nstant.in.cbor.CborEncoder;
import co.nstant.in.cbor.CborException;
import co.nstant.in.cbor.model.ByteString;
import co.nstant.in.cbor.model.DataItem;
import co.nstant.in.cbor.model.MajorType;
import co.nstant.in.cbor.model.Map;
import co.nstant.in.cbor.model.NegativeInteger;
import com.google.cose.CoseKey;
import com.google.cose.Ec2SigningKey;
import com.google.cose.OkpKeyAgreementKey;
import com.google.cose.Sign1Message;
import com.google.cose.exceptions.CoseException;
import com.google.cose.utils.Algorithm;
import com.google.cose.utils.CoseUtils;
import com.google.oak.attestation.v1.AttestationResults;
import com.google.oak.attestation.v1.Endorsements;
import com.google.oak.attestation.v1.Evidence;
import com.google.oak.attestation.v1.ReferenceValues;
import com.google.oak.util.Result;
import java.nio.charset.StandardCharsets;
import java.util.Base64;
import java.util.List;
import java.util.logging.Logger;

/**
 * Verifier implementation that doesn't verify attestation evidence and is used for testing.
 */
public class InsecureAttestationVerifier implements AttestationVerifier {
  private static final Logger logger =
      Logger.getLogger(InsecureAttestationVerifier.class.getName());

  private static final DataItem SUBJECT_PUBLIC_KEY_ID = new NegativeInteger(-4670552);

  /**
   * Doesn't perform attestation verification and just returns a success value.
   *
   * @param evidence contains claims about the Trusted Execution Environment
   * <https://www.rfc-editor.org/rfc/rfc9334.html#name-evidence>
   * @param endorsement contains statements that the endorsers vouch for the integrity of claims
   * provided in the evidence
   * <https://www.rfc-editor.org/rfc/rfc9334.html#name-endorsements>
   * @return success value wrapped in a {@code Result}
   */
  @Override
  public final Result<AttestationResults, Exception> verify(long nowUtcMillis,
      final Evidence evidence, final Endorsements endorsements,
      final ReferenceValues referenceValues) {
    logger.severe(evidence.getApplicationKeys().getEncryptionPublicKeyCertificate().toString());

    return Result.success(
        AttestationResults.newBuilder()
            .setEncryptionPublicKey(com.google.protobuf.ByteString.copyFrom(extractPublicKey(
                evidence.getApplicationKeys().getEncryptionPublicKeyCertificate().toByteArray())))
            .build());
  }

  private static byte[] extractPublicKey(byte[] certificate) {
    Sign1Message encryptionPublicKeyCert;
    try {
      encryptionPublicKeyCert = Sign1Message.deserialize(certificate);
    } catch (CborException | CoseException e) {
      throw new IllegalArgumentException("Failed to parse the public key certificate", e);
    }

    List<DataItem> dataItems;
    try {
      dataItems = CborDecoder.decode(encryptionPublicKeyCert.getMessage());
    } catch (CborException e) {
      throw new IllegalArgumentException(
          "Failed to parse the encryption public key certificate payload", e);
    }
    for (DataItem di : dataItems) {
      logger.severe(di.getMajorType() + ": " + di.toString());
      if (di.getMajorType() == MajorType.MAP) {
        Map cwtMap = (Map) di;
        if (!cwtMap.getKeys().contains(SUBJECT_PUBLIC_KEY_ID)) {
          continue;
        }
        byte[] serializedPublicKey = ((ByteString) cwtMap.get(SUBJECT_PUBLIC_KEY_ID)).getBytes();
        logger.severe(Base64.getEncoder().encodeToString(serializedPublicKey));
        try {
          DataItem publicKeyCbor = CborDecoder.decode(serializedPublicKey).get(0);
          logger.severe(publicKeyCbor.toString());

          OkpKeyAgreementKey publicKey = OkpKeyAgreementKey.decode(publicKeyCbor);
          logger.severe(Base64.getEncoder().encodeToString(publicKey.serialize()));
          return publicKey.getPublicKeyBytes();
        } catch (CborException | CoseException e) {
          throw new IllegalArgumentException("Failed to parse the public key", e);
        }
      }
    }
    throw new IllegalArgumentException("Certificate payload doesn';'t contain a public key");
  }
}
