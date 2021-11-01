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
 * @property {Uint8Array} publicKeyDer
 */

/**
 * @return {KeyPair}
 */
async function generateKeyPair() {
  const privateKey = ed25519.utils.randomPrivateKey();
  const publicKeyRaw = await ed25519.getPublicKey(privateKey);

  // Since JS does not have functions to convert to / from ASN.1, we fake this by manually
  // pre-computing and hardcoding a fixed prefix that, when concatenated with the actual raw key
  // bytes, produces a valid ASN.1-encoded Ed25519 public key.
  //
  // This is the meaning of the prefix bytes interpreted as ASN.1:
  //
  // 30 2a                : SEQUENCE len 42 (SubjectPublicKeyInfo)
  //     30 05            : SEQUENCE len 5 (AlgorithmIdentifier)
  //        06 03         : OBJECT IDENTIFIER len 3
  //           2b6570     : 1.3.101.112 = Ed25519
  //     03 21            : BIT STRING len 33
  //        00            : number of padding bits at end of content
  //        7f8d520a536d4788b8eafd93ba1d5f40b6edfd9a91af594435a8c25bdda3c8fe : [raw public key]
  //
  // Also see:
  //
  // - /oak/common/oak_sign.h
  // - https://github.com/project-oak/oak/issues/1912#issuecomment-802689201
  // - https://tools.ietf.org/html/rfc5280#section-4.1 (SubjectPublicKeyInfo)
  const publicKeyDerPrefix = new Uint8Array([
    0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00,
  ]);
  const publicKeyDer = concatenateArrays(publicKeyDerPrefix, publicKeyRaw);

  return {
    privateKey,
    publicKeyDer,
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

/**
 * @param {Uint8Array} a
 * @param {Uint8Array} b
 * @return {Uint8Array}
 */
function concatenateArrays(a, b) {
  // See https://stackoverflow.com/a/60590943/269518.
  return new Uint8Array([...a, ...b]);
}

module.exports = {
  generateKeyPair,
  hashAndSign,
};
