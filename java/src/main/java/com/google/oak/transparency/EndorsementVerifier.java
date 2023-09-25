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
import com.google.oak.util.Result;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Base64;
import java.util.Optional;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Verifier class providing functions for verifying a Transparent-Release
 * endorsement statement, and the corresponding Rekor log entry.
 */
public class EndorsementVerifier {
  private static final Logger logger = Logger.getLogger(EndorsementVerifier.class.getName());

  /**
   * Verifies a Rekor LogEntry.
   *
   * The verification involves the following steps:
   * <ul>
   * <li>verifying the signature in {@code signedEntryTimestamp} (retrieved from
   * {@code logEntryBytes}), using Rekor's public key
   * ({@code pemEncodedRekorPublicKeyBytes}).
   * <li>verifying the signature in {@code body.RekordObj.signature} (retrieved
   * from {@code logEntryBytes}), using the endorser's public key (also retrieved
   * from {@code logEntryBytes}).
   * <li>verifying that the content of the body (retrieved from
   * {@code logEntryBytes}) matches the input {@code endorsementStatementBytes}.
   * </ul>
   *
   * @param logEntryBytes
   * @param pemEncodedRekorPublicKeyBytes
   * @param endorsementStatementBytes
   * @return a Result containing true if the verification succeeds, or
   *         wrapping an Exception otherwise
   */
  public Result<Boolean, Exception> verifyRekorLogEntry(byte[] logEntryBytes,
      byte[] pemEncodedRekorPublicKeyBytes, byte[] endorsementStatementBytes) {
    return verifyRekorSignature(logEntryBytes, pemEncodedRekorPublicKeyBytes)
        .andThen(v -> RekorLogEntry.getRekorLogEntryBody(logEntryBytes))
        .andThen(body -> verifyRekorBody(body, endorsementStatementBytes));
  }

  /**
   * Unmarshales the given bytes in {@code logEntryBytes} into an instance of
   * {@code RekorLogEntry}, and if the conversion is successful, verifies the
   * signature in the resulting LogEntry using the give public key in
   * {@code pemEncodedRekorPublicKeyBytes}.
   *
   * Returns an error if either the conversion or the verification of the
   * signature fails.
   *
   * @param logEntryBytes
   * @param pemEncodedRekorPublicKeyBytes
   * @return a Result containing true if the verification succeeds, or
   *         wrapping an Exception otherwise
   */
  public Result<Boolean, Exception> verifyRekorSignature(
      byte[] logEntryBytes, byte[] pemEncodedRekorPublicKeyBytes) {
    try {
      RekorLogEntry logEntry =
          RekorLogEntry.unmarshalLogEntry(new String(logEntryBytes, StandardCharsets.UTF_8));
      logger.log(Level.INFO, "successfully unmarshaled logEntry");
      return RekorSignatureBundle.fromRekorLogEntry(logEntry).andThen(signatureBundle
          -> verifySignature(signatureBundle.getBase64Signature(),
              signatureBundle.getCanonicalizedBytes(), pemEncodedRekorPublicKeyBytes));
    } catch (RekorLogEntry.RekorValidationException e) {
      return Result.error(e);
    }
  }

  /**
   * Verifies the integrity of the Rekor body, by verifying the signature in the
   * {@code body} over the given {@code contentsBytes}, using the public key in
   * the {@code body}. This public is separately checked against a known and
   * trusted (root) public key.
   *
   * @param body
   * @param contentBytes
   * @return an empty Result if the verification succeeds, or an Exception wrapped
   *         in a Result otherwise
   */
  public Result<Boolean, Exception> verifyRekorBody(RekorLogEntry.Body body, byte[] contentBytes) {
    if (!"x509".equals(body.spec.signature.format)) {
      return Result.error(new Exception(String.format(
          "unsupported signature format: %s; only x509 is supported", body.spec.signature.format)));
    }

    // For now, we only support `sha256` as the hashing algorithm.
    if (!"sha256".equals(body.spec.data.hash.algorithm)) {
      return Result.error(
          new Exception(String.format("unsupported hash algorithm: %s; only sha256 is supported",
              body.spec.data.hash.algorithm)));
    }

    // Check that hash of the given content matches the hash of the data in the
    // Body.
    String contentsHashHex = sha256Hex(contentBytes);
    if (contentsHashHex == null || !contentsHashHex.equals(body.spec.data.hash.value)) {
      return Result.error(new Exception(String.format(
          "sha256 digest of the given bytes (%s) does not match that of the data in the body of the Rekor entry (%s)",
          contentsHashHex, body.spec.data.hash.value)));
    }

    byte[] pemEncodedPublicKeyBytes =
        Base64.getDecoder().decode(body.spec.signature.publicKey.content);

    return verifySignature(body.spec.signature.content, contentBytes, pemEncodedPublicKeyBytes);
  }

  /**
   * Computes and returns the hex-encoded SHA2-256 digest of the given bytes.
   *
   * @param bytes
   * @return the hex-encoded SHA2-256 digest of {@code bytes}
   */
  public static String sha256Hex(byte[] bytes) {
    try {
      MessageDigest md = MessageDigest.getInstance("SHA-256");
      byte[] digest = md.digest(bytes);

      // convert digest bytes to hex
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
   * @param base64SignatureBytes
   * @param contentBytes
   * @param pemEncodedPublicKeyBytes
   * @return an empty Result if the verification succeeds, or an Exception wrapped
   *         in a Result otherwise
   */
  public Result<Boolean, Exception> verifySignature(
      String base64SignatureBytes, byte[] contentBytes, byte[] pemEncodedPublicKeyBytes) {
    if (base64SignatureBytes.length() == 0) {
      return Result.error(new IllegalArgumentException("empty signature"));
    }
    if (contentBytes.length == 0) {
      return Result.error(new IllegalArgumentException("empty content"));
    }
    if (pemEncodedPublicKeyBytes.length == 0) {
      return Result.error(new IllegalArgumentException("empty public key"));
    }
    // TODO(#2854): verify the signature
    return Result.success(true);
  }
}
