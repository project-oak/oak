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

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Base64;
import java.util.Optional;
import java.util.logging.Level;
import java.util.logging.Logger;

/** Verifies a Rekor log entry against an endorsement statement. */
public class LogEntryVerifier {
  /**
   * Needs three paths as command line arguments, corresponding to the arguments
   * of {@code #verify()}. Verification failure is signalled via exit code.
   */
  public static void main(String[] args) throws Exception {
    if (args.length != 3) {
      System.exit(2);
    }

    byte[] logEntryBytes = Files.readAllBytes(Path.of(args[0]));
    byte[] publicKeyBytes = Files.readAllBytes(Path.of(args[1]));
    byte[] endorsementBytes = Files.readAllBytes(Path.of(args[2]));

    // Auto-detect PEM format of public key.
    String publicKeyString = new String(publicKeyBytes, StandardCharsets.UTF_8);
    if (SignatureVerifier.looksLikePem(publicKeyString)) {
      publicKeyBytes = SignatureVerifier.convertPemToRaw(publicKeyString);
    }

    RekorLogEntry logEntry = RekorLogEntry.createFromJson(logEntryBytes);
    Optional<Failure> failure = verify(logEntry, publicKeyBytes, endorsementBytes);
    if (failure.isPresent()) {
      logger.warning("Verification failed: " + failure.get().getMessage());
      System.exit(1);
    }
  }

  private static final Logger logger = Logger.getLogger(LogEntryVerifier.class.getName());

  private static Optional<Failure> failure(String message) {
    return Optional.of(new Failure(message));
  }

  /**
   * Verifies a Rekor log entry.
   *
   * Verifies the signature of {@code logEntry.verification.signedEntryTimestamp}
   * using the provided public key, the signature in
   * {@code logEntry.body.RekordObj.signature} using the endorser's public key
   * {@code logEntry.body.spec.signature.publicKey}, as well as digest equality of
   * {@code logEntry.body.spec.data.hash} and the endorsement statement.
   *
   * @param logEntry         the Rekor log entry
   * @param publicKeyBytes   the raw public key from Rekor
   * @param endorsementBytes the serialized endorsement statement
   * @return empty if the verification succeeds, or a failure otherwise
   */
  public static Optional<Failure> verify(
      RekorLogEntry logEntry, byte[] publicKeyBytes, byte[] endorsementBytes) {
    Optional<Failure> rekorSigVer = verifyRekorSignature(logEntry, publicKeyBytes);
    if (rekorSigVer.isPresent()) {
      return rekorSigVer;
    }
    return verifyRekorBody(logEntry.getBody(), endorsementBytes);
  }

  /**
   * Verifies the Rekor signature of a log entry using a public key.
   *
   * @param logEntry       the Rekor log entry
   * @param publicKeyBytes the raw public key
   * @return empty if the verification succeeds, or a failure otherwise
   */
  static Optional<Failure> verifyRekorSignature(RekorLogEntry logEntry, byte[] publicKeyBytes) {
    if (!logEntry.hasVerification()) {
      return failure("no verification in the log entry");
    }
    RekorSignatureBundle bundle = RekorSignatureBundle.create(logEntry);
    byte[] signatureBytes = Base64.getDecoder().decode(bundle.getBase64Signature());
    byte[] contentBytes = bundle.getCanonicalized().getBytes(StandardCharsets.UTF_8);
    return SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes);
  }

  /**
   * Verifies the integrity of the Rekor body, by verifying the signature in the
   * {@code body} over the given {@code contentBytes}, using the public key in
   * the {@code body}.
   *
   * @param body         the body of the Rekor log entry
   * @param contentBytes the serialized content
   * @return empty if the verification succeeds, or a failure otherwise
   */
  static Optional<Failure> verifyRekorBody(RekorLogEntry.Body body, byte[] contentBytes) {
    if (!"x509".equals(body.spec.signature.format)) {
      return failure(String.format(
          "unsupported signature format: %s; only x509 is supported", body.spec.signature.format));
    }

    // For now, we only support `sha256` as the hashing algorithm.
    if (!"sha256".equals(body.spec.data.hash.algorithm)) {
      return failure(String.format("unsupported hash algorithm: %s; only sha256 is supported",
          body.spec.data.hash.algorithm));
    }

    // Content digest must match the hash mentioned in the body.
    String digest = sha256Hex(contentBytes);
    if (digest == null || !digest.equals(body.spec.data.hash.value)) {
      return failure(String.format(
          "SHA2-256 digest of contents (%s) differs from that in Rekor entry body (%s)",
          digest, body.spec.data.hash.value));
    }

    byte[] signatureBytes = Base64.getDecoder().decode(body.spec.signature.content);
    byte[] publicKeyBytes = SignatureVerifier.convertPemToRaw(new String(
        Base64.getDecoder().decode(body.spec.signature.publicKey.content),
        StandardCharsets.UTF_8));
    return SignatureVerifier.verify(signatureBytes, publicKeyBytes, contentBytes);
  }

  /**
   * Computes the hex-encoded SHA2-256 digest.
   *
   * @param bytes the binary content to compute the digest from
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

  private LogEntryVerifier() {
  }
}
