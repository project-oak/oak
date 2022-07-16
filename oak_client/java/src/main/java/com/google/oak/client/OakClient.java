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

import java.util.Optional;

/**
 * Abstract client for sending and receiving encrypted messages to a server. This class provides an
 * abstract builder that must be implemented by concrete subclasses of this class. The builder takes
 * a {@code RpcClient} supplier, an {@code Encryptor} supplier, and optionally an evidence
 * supplier to build a concrete instance of {@code OakClient}. If an evidence supplier is provider,
 * the client has to verify the correctness of the evidence prior to sending messages to the server.
 *
 * @param R type of the requests that this client sends
 * @param T type of the responses that this client receives
 */
public abstract class OakClient<R, T> implements AutoCloseable {
  // TODO(#3063): Replace return type with Result<T>
  /**
   * Sends a request to a remote server and receives the response.
   * @param request the request to send to server
   * @return the response received from the server wrapped in an Optional
   */
  abstract Optional<T> send(final R request);

  /**
   * Abstract builder class that allows subclasses to override it, providing customized {@code
   * build} and {@code self} methods.
   */
  abstract static class Builder<R, T, B extends Builder<R, T, B>> {
    final EncryptorProvider encryptorProvider;
    final RpcClientProvider<R, T> rpcClientProvider;
    Optional<EvidenceProvider> evidenceProvider = Optional.empty();

    /**
     * @param encryptorProvider provides an Encryptor instance
     * @param rpcClientProvider provides an instance of RpcClient
     */
    Builder(final EncryptorProvider encryptorProvider,
        final RpcClientProvider<R, T> rpcClientProvider) {
      this.encryptorProvider = encryptorProvider;
      this.rpcClientProvider = rpcClientProvider;
    }

    public B withEvidenceProvider(final EvidenceProvider evidenceProvider) {
      this.evidenceProvider = Optional.of(evidenceProvider);
      return self();
    }

    /**
     * Builds and returns and instance of OakClient. The build should initialize the client with an
     * encryptor and verify any evidence provided by the evidence supplier, if one is present. Or
     * the concrete subclass should provide additional appropriate methods for initializing the
     * client instance.
     *
     * @return an instance of OakClient.
     */
    abstract OakClient<R, T> build();

    // Subclasses must override this method to return "this".
    protected abstract B self();
  }

  // The following functional interfaces could individually have been replaced by a {@code
  // Supplier<T>}, but to allow a single class implement more than one of these interfaces,
  // dedicated functional interfaces are preferred.
  // TODO(#3063): Replace Optional<T> with Result<T> in the following.

  /**
   * An interface for providing instances of {@code RpcClient}.
   */
  public interface RpcClientProvider<R, T> {
    /**
     * @return an instance of {@code RpcClient} wrapped in an Optional.
     */
    Optional<? extends RpcClient<R, T>> getRpcClient();
  }

  /**
   * An interface for providing {@code Encryptor} instances.
   */
  public interface EncryptorProvider {
    /**
     *
     * @return an instance of Encryptor wrapped in an Optional.
     */
    Optional<? extends Encryptor> getEncryptor();
  }

  /**
   * An interface for providing instances of Evidence.
   *
   * A evidence normally includes an instance of EndorsementEvidence and optionally some server
   * configuration information. If the client policy requires verification of the server
   * configuration, then the client should be built with a provider that does provide server
   * configuration.
   */
  public interface EvidenceProvider {
    /**
     * Returns evidence about the trustworthiness of a remote server.
     *
     * @return the evidence wrapped in an Optional.
     */
    Optional<? extends Evidence> getEvidence();
  }
}
