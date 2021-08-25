//
// Copyright 2021 The Project Oak Authors
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

import com.google.crypto.tink.subtle.EcdsaVerifyJce;
import com.google.crypto.tink.subtle.EllipticCurves;
import com.google.crypto.tink.subtle.EllipticCurves.CurveType;
import com.google.crypto.tink.subtle.EllipticCurves.EcdsaEncoding;
import com.google.crypto.tink.subtle.Enums.HashType;
import java.security.GeneralSecurityException;
import java.security.interfaces.ECPublicKey;

public class SignatureVerifier {
  /** Size of the Elliptic Curve coordinate value. */
  private static final int EC_POINT_SIZE = 32;
  /** Elliptic Curve type. */
  private static final CurveType CURVE_TYPE = CurveType.NIST_P256;
  /** Encoding of the verified certificate. */
  private static final EcdsaEncoding CERTIFICATE_ENCODING = EcdsaEncoding.IEEE_P1363;
  /** Hash type used in certificates. */
  private static final HashType HASH_TYPE = HashType.SHA256;

  private final EcdsaVerifyJce verifier;

  /**
   * Creates a ECDSA-P256 signature verifier.
   *
   * `publicKey` parameter must be an OpenSSL ECDSA-P256 key, which is represented as
   * "0x04 | X: 32-byte | Y: 32-byte".
   * Where X and Y are big-endian coordinates of an Elliptic Curve point.
   * https://datatracker.ietf.org/doc/html/rfc6979
   */
  public SignatureVerifier(byte[] publicKey) throws GeneralSecurityException {
    // Extract Elliptic Curve point coordinates from an OpenSSL public key.
    byte[] x = new byte[EC_POINT_SIZE];
    byte[] y = new byte[EC_POINT_SIZE];
    System.arraycopy(publicKey, 1, x, 0, EC_POINT_SIZE);
    System.arraycopy(publicKey, EC_POINT_SIZE + 1, y, 0, EC_POINT_SIZE);
    ECPublicKey parsedPublicKey = EllipticCurves.getEcPublicKey(CURVE_TYPE, x, y);

    // Create a signature verifier.
    verifier = new EcdsaVerifyJce(parsedPublicKey, HASH_TYPE, CERTIFICATE_ENCODING);
  }

  /**
   * Verifies the `signature` value over `input` data.
   *
   * `signature` parameter must be an IEEE-P1363 signature.
   * https://standards.ieee.org/standard/1363-2000.html
   */
  public Boolean verify(byte[] input, byte[] signature) {
    try {
      verifier.verify(signature, input);
      return true;
    } catch (GeneralSecurityException e) {
      return false;
    }
  }
}
