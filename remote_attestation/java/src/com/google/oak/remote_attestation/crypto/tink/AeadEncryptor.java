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

package com.google.oak.remote_attestation.crypto;

import com.google.crypto.tink.subtle.AesGcmJce;
import java.security.GeneralSecurityException;

/**
 * Implementation of Authenticated Encryption with Associated Data (AEAD).
 * https://datatracker.ietf.org/doc/html/rfc5116
 */
public class AeadEncryptor {
    private final AesGcmJce encryptor;

    public AeadEncryptor(byte[] key) throws GeneralSecurityException {
        encryptor = new AesGcmJce(key);
    }

    /**
     * Encrypts `data` using `AeadEncryptor::encryptor`.
     * The resulting encrypted data is prefixed with a random 12 bit nonce.
     */
    public byte[] encrypt(byte[] data) throws GeneralSecurityException {
        // Additional authenticated data is not required for the remotely attested channel,
        // since after session key is established client and server exchange messages with a
        // single encrypted field.
        return encryptor.encrypt(data, null);
    }

    /**
     * Decrypts and authenticates `data` using `AeadEncryptor::encryptor`.
     * `data` must contain an encrypted message prefixed with a 12 bit nonce.
     */
    public byte[] decrypt(byte[] data) throws GeneralSecurityException {
        // Additional authenticated data is not required for the remotely attested channel,
        // since after session key is established client and server exchange messages with a
        // single encrypted field.
        return encryptor.decrypt(data, null);
    }
}
