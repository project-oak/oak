//
// Copyright 2022 The Project Oak Authors
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

package com.google.oak.client;

import com.google.oak.evidence.Evidence;
import com.google.oak.util.Result;

/**
 * Abstract client for sending and receiving encrypted messages to a server. We recommend concrete
 * subclasses of this class to provide builders for creating instances of the class. The builders
 * should use a {@code RpcClientProvider}, an {@code EncryptorProvider}, and optionally an {@code
 * EvidenceProvider} to build a concrete instance of {@code OakClient}. If an evidence supplier is
 * provided, the client has to verify the correctness of the evidence prior to getting an instance
 * of {@code Encryptor} and sending messages to the server. In a complete, and production-ready
 * implementation, an {@code EvidenceProvider} MUST be provided and verified.
 *
 * @param R type of the requests that this client sends
 * @param T type of the responses that this client receives
 */
public interface OakClient<R, T> extends AutoCloseable {
  /**
   * Sends a request to a remote server and receives the response.
   *
   * @param request the request to send to the server
   * @return the response received from the server wrapped in a {@code Result}
   */
  abstract Result<T, Exception> send(final R request);

  // The following functional interfaces could have individually been replaced by a Supplier<T>, but
  // to allow a single class implement more than one of these interfaces, dedicated functional
  // interfaces are preferred.

  /** An interface for providing instances of {@code RpcClient}. */
  public interface RpcClientProvider<C extends RpcClient> {
    /**
     * @return an instance of {@code RpcClient} wrapped in a {@code Result}
     */
    Result<C, Exception> getRpcClient();
  }

  /** An interface for providing {@code Encryptor} instances. */
  public interface EncryptorProvider<E extends Encryptor> {
    /**
     * @param signingPublicKey signing public key of the server
     * @return an instance of Encryptor wrapped in a {@code Result}
     */
    Result<E, Exception> getEncryptor(byte[] signingPublicKey);
  }

  /**
   * An interface for providing instances of Evidence.
   *
   * <p>An evidence normally includes the public key part of the server's signing key, an instance
   * of {@code EndorsementEvidence}, and optionally some server configuration information. If the
   * client policy requires verification of the server configuration, then the client should be
   * built with a provider that does provide server configuration.
   */
  public interface EvidenceProvider<E extends Evidence> {
    /**
     * Returns evidence about the trustworthiness of a remote server.
     *
     * @return the evidence wrapped in a {@code Result}
     */
    Result<E, Exception> getEvidence();
  }
}
