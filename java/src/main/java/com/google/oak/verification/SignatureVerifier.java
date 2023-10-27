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

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.KeyFactory;
import java.security.PublicKey;
import java.security.Signature;
import java.security.spec.X509EncodedKeySpec;
import java.util.Base64;
import java.util.Optional;
import java.util.logging.Logger;

/** Verifies a signature based on a public key. */
public class SignatureVerifier {
  /**
   * Needs three paths as command line arguments, corresponding to the arguments
   * of {@code #verify()}. Verification failure is signalled via exit code.
   */
  public static void main(String[] args) throws Exception {
    if (args.length != 3) {
      System.exit(2);
    }

    byte[] signatureBytes = Files.readAllBytes(Path.of(args[0]));
    byte[] publicKeyBytes = Files.readAllBytes(Path.of(args[1]));
    byte[] contentBytes = Files.readAllBytes(Path.of(args[2]));

    // Auto-detect PEM format of public key.
    String publicKeyString = new String(publicKeyBytes, StandardCharsets.UTF_8);
    if (looksLikePem(publicKeyString)) {
      publicKeyBytes = convertPemToRaw(publicKeyString);
    }

    Optional<Failure> failure = verify(signatureBytes, publicKeyBytes, contentBytes);
    if (failure.isPresent()) {
      logger.warning("Verification failed: " + failure.get().getMessage());
      System.exit(1);
    }
  }

  private static final Logger logger = Logger.getLogger(SignatureVerifier.class.getName());

  private static Optional<Failure> failure(String message) {
    return Optional.of(new Failure(message));
  }

  /**
   * Verifies the signature over content bytes using a public key.
   *
   * @param signatureBytes the raw ECDSA signature, likely 71 bytes long
   * @param publicKeyBytes the raw public key
   * @param contentBytes   the serialized content
   * @return empty if the verification succeeds, or a failure otherwise
   */
  public static Optional<Failure> verify(
      byte[] signatureBytes, byte[] publicKeyBytes, byte[] contentBytes) {
    if (signatureBytes == null || signatureBytes.length == 0) {
      return failure("empty signature");
    }
    if (publicKeyBytes == null || publicKeyBytes.length == 0) {
      return failure("empty public key");
    }
    if (contentBytes == null || contentBytes.length == 0) {
      return failure("empty content");
    }

    X509EncodedKeySpec keySpec = new X509EncodedKeySpec(publicKeyBytes);
    Exception exception = null;
    boolean success = false;
    try {
      KeyFactory keyFactory = KeyFactory.getInstance("EC");
      PublicKey publicKey = keyFactory.generatePublic(keySpec);
      Signature s = Signature.getInstance("SHA256withECDSA");
      s.initVerify(publicKey);
      s.update(contentBytes);
      success = s.verify(signatureBytes);
    } catch (Exception e) {
      exception = e;
    }

    return success
        ? Optional.empty()
        : failure(exception != null
                ? String.format("%s: %s", exception.getClass().getName(), exception.getMessage())
                : "Signature verification failed");
  }

  private static final String PEM_HEADER = "-----BEGIN PUBLIC KEY-----";
  private static final String PEM_FOOTER = "-----END PUBLIC KEY-----";

  /** Makes a plausible guess whether the public key is in PEM format. */
  static boolean looksLikePem(String maybePem) {
    String p = maybePem.trim();
    return p.startsWith(PEM_HEADER) && p.endsWith(PEM_FOOTER);
  }

  /** Converts a public key from PEM (on disk format) to raw binary format. */
  static byte[] convertPemToRaw(String pem) {
    String trimmed = pem.replace(PEM_HEADER, "").replace(PEM_FOOTER, "").replace("\n", "").trim();
    return Base64.getDecoder().decode(trimmed);
  }

  private SignatureVerifier() {}
}
