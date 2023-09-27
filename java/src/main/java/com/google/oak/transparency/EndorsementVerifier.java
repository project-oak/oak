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

package com.google.oak.transparency;

import com.google.oak.session.v1.AttestationEndorsement;
import com.google.oak.session.v1.AttestationEvidence;
import com.google.oak.transparency.RekorLogEntry.Body;
import com.google.oak.util.Result;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Base64;
import java.util.Optional;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Verifies a Transparent-Release endorsement statement and the corresponding
 * Rekor log entry.
 */
public class EndorsementVerifier {
  private static final Logger logger = Logger.getLogger(EndorsementVerifier.class.getName());

  /**
   * Verifies a Rekor LogEntry.
   *
   * Verifies the following items:
   * <ul>
   * <li>The signature in {@code signedEntryTimestamp} (retrieved from
   * {@code logEntryBytes}), using Rekor's public key ({@code publicKeyBytes}).
   * <li>The signature in {@code body.RekordObj.signature} (retrieved
   * from {@code logEntryBytes}), using the endorser's public key (also retrieved
   * from {@code logEntryBytes}).
   * <li>Equality of the content of the body (retrieved from
   * {@code logEntryBytes}) and the input {@code endorsementBytes}.
   * </ul>
   *
   * @param logEntry         The Rekor log entry
   * @param publicKeyBytes   The PEM-encoded public key from Rekor
   * @param endorsementBytes The serialized endorsement statement
   * @return Empty if the verification succeeds, or an error message otherwise
   */
  public static Optional<String> verifyRekorLogEntry(
      RekorLogEntry logEntry, byte[] publicKeyBytes, byte[] endorsementBytes) {
    Optional<String> rekorSigVer = verifyRekorSignature(logEntry, publicKeyBytes);
    logger.warning("HEYJA ");
    if (rekorSigVer.isPresent()) {
      logger.warning("HEY " + rekorSigVer.get());
      return rekorSigVer;
    }
    logger.warning("DIG " + sha256Hex(endorsementBytes));
    Optional<String> b = verifyRekorBody(logEntry.getBody(), endorsementBytes);
    if (b.isPresent()) {
      logger.warning("HUU " + b.get());
    }
    return b;
  }

  /**
   * Unmarshals the given bytes in {@code logEntryBytes} into an instance of
   * {@code RekorLogEntry}, and if the conversion is successful, verifies the
   * signature in the resulting LogEntry using the give public key in
   * {@code publicKeyBytes}.
   *
   * @param logEntry       The Rekor log entry
   * @param publicKeyBytes The PEM-encoded public key
   * @return Empty if the verification succeeds, or an error message otherwise
   */
  public static Optional<String> verifyRekorSignature(RekorLogEntry logEntry, byte[] publicKeyBytes) {
    if (!logEntry.hasVerification()) {
      return Optional.of("no verification in the log entry");
    }
    RekorSignatureBundle bundle = RekorSignatureBundle.create(logEntry);
    return verifySignature(bundle.getBase64Signature(), bundle.getCanonicalizedBytes(), publicKeyBytes);
  }

  /**
   * Verifies the integrity of the Rekor body, by verifying the signature in the
   * {@code body} over the given {@code contentsBytes}, using the public key in
   * the {@code body}. This public is separately checked against a known and
   * trusted (root) public key.
   *
   * @param body         The body of the Rekor log entry
   * @param contentBytes The serialized content
   * @return Empty if the verification succeeds, or an error message otherwise
   */
  static Optional<String> verifyRekorBody(RekorLogEntry.Body body, byte[] contentBytes) {
    if (!"x509".equals(body.spec.signature.format)) {
      return Optional.of(String.format(
          "unsupported signature format: %s; only x509 is supported", body.spec.signature.format));
    }

    // For now, we only support `sha256` as the hashing algorithm.
    if (!"sha256".equals(body.spec.data.hash.algorithm)) {
      return Optional.of(
          String.format("unsupported hash algorithm: %s; only sha256 is supported",
              body.spec.data.hash.algorithm));
    }

    // Check that hash of the given content matches the hash of the data in the
    // Body.
    String digest = sha256Hex(contentBytes);
    if (digest == null || !digest.equals(body.spec.data.hash.value)) {
      return Optional.of(String.format(
          "SHA2-256 digest of contents (%s) differs from that in Rekor entry body (%s)",
          digest, body.spec.data.hash.value));
    }

    byte[] publicKeyBytes = Base64.getDecoder().decode(body.spec.signature.publicKey.content);
    return verifySignature(body.spec.signature.content, contentBytes, publicKeyBytes);
  }

  /**
   * Computes the hex-encoded SHA2-256 digest.
   *
   * @param bytes The binary content to compute the digest from
   * @return the hex-encoded SHA2-256 digest of {@code bytes}
   */
  public static String sha256Hex(byte[] bytes) {
    try {
      MessageDigest md = MessageDigest.getInstance("SHA-256");
      byte[] digest = md.digest(bytes);
      StringBuilder result = new StringBuilder();
      for (byte b : digest) {
        result.append(String.format("%02x", b));
      }
      return result.toString();
    } catch (NoSuchAlgorithmException e) {
      logger.log(Level.SEVERE, e.getMessage());
      return null;
    }
  }

  /**
   * Verifies the given base64-encoded signature over the given content bytes,
   * using the given PEM-encoded public key.
   *
   * @param signature      The base64-encoded signature
   * @param contentBytes   The serialized content
   * @param publicKeyBytes The PEM-encoded public key
   * @return Empty if the verification succeeds, or an error message otherwise
   */
  public static Optional<String> verifySignature(
      String signature, byte[] contentBytes, byte[] publicKeyBytes) {
    if (signature == null || signature.length() == 0) {
      return Optional.of("empty signature");
    }
    if (contentBytes == null || contentBytes.length == 0) {
      return Optional.of("empty content");
    }
    if (publicKeyBytes == null || publicKeyBytes.length == 0) {
      return Optional.of("empty public key");
    }
    // TODO(#2854): verify the signature
    return Optional.empty();
  }
}
