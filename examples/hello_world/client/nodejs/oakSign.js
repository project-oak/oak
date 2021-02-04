/*
 * Copyright 2019 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied25519.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

const ed25519 = require('noble-ed25519');
const { createHash } = require('crypto');

/**
 * @typedef {Object} KeyPair
 * @property {Uint8Array} privateKey
 * @property {Uint8Array} publicKey
 */

/**
 * @return {KeyPair}
 */
async function generateKeyPair() {
  const privateKey = ed25519.utils.randomPrivateKey();
  const publicKey = await ed25519.getPublicKey(privateKey);

  return {
    privateKey,
    publicKey,
  };
}

/**
 * @param {Uint8Array} input
 * @param {Uint8Array} privateKey
 * @return {Uint8Array}
 */
async function hashAndSign(input, privateKey) {
  const challengeHash = createHash('sha256').update(input).digest();
  const signedHash = await ed25519.sign(challengeHash, privateKey);

  return signedHash;
}

module.exports = {
  generateKeyPair,
  hashAndSign,
};
