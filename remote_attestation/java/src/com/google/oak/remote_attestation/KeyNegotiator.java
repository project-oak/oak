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

import static java.nio.charset.StandardCharsets.UTF_8;

import com.google.common.primitives.Bytes;
import com.google.crypto.tink.subtle.Hkdf;
import com.google.crypto.tink.subtle.X25519;
import java.security.GeneralSecurityException;

/**
 * Implementation of the X25519 Elliptic Curve Diffie-Hellman (ECDH) key negotiation.
 * https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
 */
public class KeyNegotiator {
  // MAC algorithm used in HKDF.
  private static final String KEY_DERIVATION_ALGORITHM = "HMACSHA256";
  // Salt used for key derivation with HKDF.
  // https://datatracker.ietf.org/doc/html/rfc5869
  private static final String KEY_DERIVATION_SALT = "Remote Attestation Protocol v1";
  /// Purpose string used for deriving server session keys with HKDF.
  private static final String SERVER_KEY_PURPOSE = "Remote Attestation Protocol Server Session Key";
  /// Purpose string used for deriving client session keys with HKDF.
  private static final String CLIENT_KEY_PURPOSE = "Remote Attestation Protocol Client Session Key";
  // AES-256 with GCM key size.
  // https://datatracker.ietf.org/doc/html/rfc5288
  private static final int KEY_SIZE_BYTES = 32;
  private final byte[] privateKey;

  /** Defines the type of encryptor created by {@code KeyNegotiator.createEncryptor}. */
  public enum EncryptorType {
    // Defines a server encryptor, which uses server session key for encryption and client
    // session key for decryption.
    SERVER,
    // Defines a client encryptor, which uses client session key for encryption and server
    // session key for decryption.
    CLIENT,
  }

  public KeyNegotiator() {
    privateKey = X25519.generatePrivateKey();
  }

  public byte[] getPublicKey() throws GeneralSecurityException {
    return X25519.publicFromPrivate(privateKey);
  }

  /**
   * Derives a session key from {@code key_material} using HKDF.
   * https://datatracker.ietf.org/doc/html/rfc5869
   * https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
   *
   * In order to derive keys, uses the information string that consists of a purpose string, a
   * server public key and a client public key (in that specific order).
   */
  byte[] keyDerivationFunction(byte[] keyMaterial, String keyPurpose, byte[] firstPublicKey,
      byte[] secondPublicKey) throws GeneralSecurityException {
    // Session key is derived from a purpose string, public key and peer public key.
    byte[] info = Bytes.concat(keyPurpose.getBytes(UTF_8), firstPublicKey, secondPublicKey);
    return Hkdf.computeHkdf(KEY_DERIVATION_ALGORITHM, keyMaterial,
        KEY_DERIVATION_SALT.getBytes(UTF_8), info, KEY_SIZE_BYTES);
  }

  /**
   * Derives a session key and creates an {@code AeadEncryptor::encryptor} from it.
   * https://datatracker.ietf.org/doc/html/rfc7748#section-6.1
   */
  public AeadEncryptor createEncryptor(byte[] peerPublicKey, EncryptorType encryptorType)
      throws GeneralSecurityException {
    // Agree on key material.
    byte[] keyMaterial = X25519.computeSharedSecret(privateKey, peerPublicKey);
    byte[] selfPublicKey = getPublicKey();

    // Derive session keys.
    byte[] encryptionKey = null;
    byte[] decryptionKey = null;
    switch (encryptorType) {
      // On the server side {@code self_public_key} is the server key.
      case SERVER:
        encryptionKey =
            keyDerivationFunction(keyMaterial, SERVER_KEY_PURPOSE, selfPublicKey, peerPublicKey);
        decryptionKey =
            keyDerivationFunction(keyMaterial, CLIENT_KEY_PURPOSE, selfPublicKey, peerPublicKey);
        break;
      // On the client side {@code peer_public_key} is the server key.
      case CLIENT:
        encryptionKey =
            keyDerivationFunction(keyMaterial, CLIENT_KEY_PURPOSE, peerPublicKey, selfPublicKey);
        decryptionKey =
            keyDerivationFunction(keyMaterial, SERVER_KEY_PURPOSE, peerPublicKey, selfPublicKey);
        break;
    }

    return new AeadEncryptor(encryptionKey, decryptionKey);
  }
}
