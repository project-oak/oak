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

import com.google.oak.util.Result;
import java.util.Optional;

/**
 * Abstract client for sending and receiving encrypted messages to a server. This class provides an
 * abstract builder that must be implemented by concrete subclasses of this class. The builder takes
 * a {@code RpcClientProvider}, an {@code EncryptorProvider}, and optionally an {@code
 * EvidenceProvider} to build a concrete instance of {@code OakClient}. If an evidence supplier is
 * provided, the client has to verify the correctness of the evidence prior to getting an instance
 * of {@code Encryptor} and sending messages to the server. In a complete, and production-ready
 * implementation, an {@code EvidenceProvider} MUST be provided and verified.
 *
 * @param R type of the requests that this client sends
 * @param T type of the responses that this client receives
 */
public abstract class OakClient<R, T> implements AutoCloseable {
  /**
   * Sends a request to a remote server and receives the response.
   *
   * @param request the request to send to the server
   * @return the response received from the server wrapped in a {@code Result}
   */
  abstract Result<T, Exception> send(final R request);

  /**
   * Abstract builder class that allows subclasses to override it, providing customized {@code
   * build} and {@code self} methods.
   */
  abstract static class Builder<R, T, B extends Builder<R, T, B>> {
    final EncryptorProvider encryptorProvider;
    final RpcClientProvider rpcClientProvider;
    Optional<EvidenceProvider> evidenceProvider = Optional.empty();

    /**
     * @param encryptorProvider instance that can provide an {@code Encryptor} instance
     * @param rpcClientProvider instance that can provide an instance of {@code RpcClient}
     */
    Builder(final EncryptorProvider encryptorProvider, final RpcClientProvider rpcClientProvider) {
      this.encryptorProvider = encryptorProvider;
      this.rpcClientProvider = rpcClientProvider;
    }

    /**
     * Configure this builder to use the given {@code EvidenceProvider}.
     *
     * @param evidenceProvider instance that can provide an {@code Evidence} instance
     * @return this builder
     */
    public B withEvidenceProvider(final EvidenceProvider evidenceProvider) {
      this.evidenceProvider = Optional.of(evidenceProvider);
      return self();
    }

    /**
     * Builds and returns and instance of {@code OakClient}. The build should verify any evidence
     * provided by the {@code EvidenceProvider}, if one is present, and initialize the client with
     * an {@code Encryptor}. Alternatively, the concrete subclass may provide additional appropriate
     * methods for initializing the client instance before using it for sending and receiving
     * messages. However, partial construction of the client is discouraged.
     *
     * @return an instance of {@code OakClient}.
     */
    abstract OakClient<R, T> build();

    // Subclasses must override this method to return "this".
    protected abstract B self();
  }

  // The following functional interfaces could have individually been replaced by a Supplier<T>, but
  // to allow a single class implement more than one of these interfaces, dedicated functional
  // interfaces are preferred.

  /**
   * An interface for providing instances of {@code RpcClient}.
   */
  public interface RpcClientProvider {
    /**
     * @return an instance of {@code RpcClient} wrapped in a {@code Result}
     */
    Result<? extends RpcClient, Exception> getRpcClient();
  }

  /**
   * An interface for providing {@code Encryptor} instances.
   */
  public interface EncryptorProvider {
    /**
     * @param signingPublicKey signing public key of the server
     * @return an instance of Encryptor wrapped in a {@code Result}
     */
    Result<? extends Encryptor, Exception> getEncryptor(byte[] signingPublicKey);
  }

  /**
   * An interface for providing instances of Evidence.
   *
   * <p>An evidence normally includes the public key part of the server's signing key, an instance
   * of {@code EndorsementEvidence}, and optionally some server configuration information. If the
   * client policy requires verification of the server configuration, then the client should be
   * built with a provider that does provide server configuration.
   */
  public interface EvidenceProvider {
    /**
     * Returns evidence about the trustworthiness of a remote server.
     *
     * @return the evidence wrapped in a {@code Result}
     */
    Result<? extends Evidence, Exception> getEvidence();
  }
}
