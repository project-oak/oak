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

package com.google.oak.crypto.hpke;

import com.google.oak.util.Result;

// TODO(#3642): Implement Java Hybrid Encryption.
public final class Hpke {
  public static final class SenderContext {
    public final byte[] serializedEncapsulatedPublicKey;
    public final Context.SenderRequestContext senderRequestContext;
    public final Context.SenderResponseContext senderResponseContext;

    SenderContext(final byte[] serializedEncapsulatedPublicKey,
        Context.SenderRequestContext senderRequestContext,
        Context.SenderResponseContext senderResponseContext) {
      this.serializedEncapsulatedPublicKey = serializedEncapsulatedPublicKey;
      this.senderRequestContext = senderRequestContext;
      this.senderResponseContext = senderResponseContext;
    }
  }

  /**
   * Sets up an HPKE sender by generating an ephemeral keypair (and serializing the corresponding
   * public key) and creating a sender context.
   *
   * @return encapsulated public key, sender request and sender response contexts, where an
   *     encapsulated public key is represented as a NIST P-256 SEC1 encoded point public key; see
   * <https://secg.org/sec1-v2.pdf>
   * <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
   */
  public static final Result<SenderContext, Exception> setupBaseSender(
      final byte[] serializedRecipientPublicKey, final byte[] info) {
    return Result.success(new SenderContext(
        new byte[0], new Context.SenderRequestContext(), new Context.SenderResponseContext()));
  }

  public static final class RecipientContext {
    public final Context.RecipientRequestContext recipientRequestContext;
    public final Context.RecipientResponseContext recipientResponseContext;

    RecipientContext(Context.RecipientRequestContext recipientRequestContext,
        Context.RecipientResponseContext recipientResponseContext) {
      this.recipientRequestContext = recipientRequestContext;
      this.recipientResponseContext = recipientResponseContext;
    }
  }

  /**
   * Sets up an HPKE recipient by creating a recipient context.
   * <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
   *
   * @return recipient request and recipient response contexts; see
   * <https://www.rfc-editor.org/rfc/rfc9180.html#name-encryption-to-a-public-key>
   *
   */
  public static final Result<RecipientContext, Exception> setupBaseRecipient(
      final byte[] serializedEncapsulatedPublicKey, KeyPair recipientKeyPair, final byte[] info) {
    return Result.success(new RecipientContext(
        new Context.RecipientRequestContext(), new Context.RecipientResponseContext()));
  }

  private Hpke() {}
}
