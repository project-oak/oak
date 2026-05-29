/*
 * Copyright 2026 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.google.oak.session.tls

import java.io.ByteArrayInputStream
import java.io.FileInputStream
import java.net.Socket
import java.security.KeyFactory
import java.security.KeyStore
import java.security.cert.CertificateException
import java.security.cert.CertificateFactory
import java.security.cert.X509Certificate
import java.security.spec.PKCS8EncodedKeySpec
import java.util.Base64
import javax.net.ssl.KeyManager
import javax.net.ssl.KeyManagerFactory
import javax.net.ssl.SSLContext
import javax.net.ssl.SSLEngine
import javax.net.ssl.TrustManager
import javax.net.ssl.TrustManagerFactory
import javax.net.ssl.X509ExtendedKeyManager
import javax.net.ssl.X509ExtendedTrustManager
import javax.net.ssl.X509TrustManager

/**
 * Callback to send TLS data over the wire.
 *
 * Used by [OakSessionTlsContext.newInitializedSession] to drive the handshake automatically.
 */
fun interface SendFunction {
  /** Sends data to the peer. */
  suspend fun send(data: ByteArray)
}

/**
 * Callback to receive TLS data from the wire.
 *
 * Used by [OakSessionTlsContext.newInitializedSession] to drive the handshake automatically.
 */
fun interface ReceiveFunction {
  /** Receives data from the peer. */
  suspend fun receive(): ByteArray
}

/**
 * Manages an SSL Context that will be used to create Oak TLS sessions.
 *
 * For most use cases, use [newInitializedSession] which handles the TLS handshake automatically.
 * Use [newSession] only if you need fine-grained control over the handshake process (e.g., for
 * async I/O or custom framing).
 *
 * This class wraps standard JSSE and supports custom security providers (e.g. Conscrypt) to ensure
 * the same underlying cryptographic operations as the C++ `OakSessionTlsContext`.
 */
interface OakSessionTlsContext {

  /**
   * Creates a new session and performs the TLS handshake using the provided send/receive callbacks.
   *
   * @param send callback to send TLS data to the peer
   * @param receive callback to receive TLS data from the peer
   * @return an initialized session ready for encrypt/decrypt operations
   * @throws OakSessionTlsException if the handshake fails
   */
  @Throws(OakSessionTlsException::class)
  suspend fun newInitializedSession(
    send: SendFunction,
    receive: ReceiveFunction,
  ): OakSessionTlsInitializer.InitializedSession

  /**
   * Creates a new [OakSessionTlsInitializer] for manual handshake control.
   *
   * Use this only if you need to drive the handshake yourself (e.g., for async I/O or custom
   * transport framing). For most use cases, prefer [newInitializedSession] instead.
   *
   * @return a new initializer for manual handshake
   * @throws OakSessionTlsException if session creation fails
   */
  @Throws(OakSessionTlsException::class) fun newSession(): OakSessionTlsInitializer

  companion object {
    /**
     * Creates a client-side TLS context.
     *
     * @param config the client configuration
     * @return a new context configured for client mode
     * @throws OakSessionTlsException if context creation fails
     */
    @JvmStatic
    @Throws(OakSessionTlsException::class)
    fun create(config: OakSessionClientTlsContext.Config): OakSessionTlsContext {
      try {
        return OakSessionClientTlsContext(config)
      } catch (e: OakSessionTlsException) {
        throw e
      } catch (e: Exception) {
        throw OakSessionTlsException("failed to create client TLS context", e)
      }
    }

    /**
     * Creates a server-side TLS context.
     *
     * @param config the server configuration
     * @return a new context configured for server mode
     * @throws OakSessionTlsException if context creation fails
     */
    @JvmStatic
    @Throws(OakSessionTlsException::class)
    fun create(config: OakSessionServerTlsContext.Config): OakSessionTlsContext {
      try {
        return OakSessionServerTlsContext(config)
      } catch (e: OakSessionTlsException) {
        throw e
      } catch (e: Exception) {
        throw OakSessionTlsException("failed to create server TLS context", e)
      }
    }

    /**
     * Loads a DER-encoded private key from a PEM file.
     *
     * @param path path to the PEM-encoded private key file
     * @return the DER-encoded private key bytes (PKCS#8)
     */
    @JvmStatic
    @Throws(OakSessionTlsException::class)
    fun loadPrivateKeyFromFile(path: String): ByteArray {
      try {
        val pem = FileInputStream(path).use { it.readBytes().decodeToString() }
        val base64 =
          pem
            .replace(Regex("-----BEGIN [A-Z ]+-----"), "")
            .replace(Regex("-----END [A-Z ]+-----"), "")
            .replace(Regex("\\s"), "")
        return Base64.getDecoder().decode(base64)
      } catch (e: Exception) {
        throw OakSessionTlsException("failed to load private key from $path", e)
      }
    }

    /**
     * Loads a DER-encoded certificate from a PEM file.
     *
     * @param path path to the PEM-encoded certificate file
     * @return the DER-encoded X.509 certificate bytes
     */
    @JvmStatic
    @Throws(OakSessionTlsException::class)
    fun loadCertificateFromFile(path: String): ByteArray {
      try {
        val cf = CertificateFactory.getInstance("X.509")
        return FileInputStream(path).use { fis ->
          (cf.generateCertificate(fis) as X509Certificate).encoded
        }
      } catch (e: Exception) {
        throw OakSessionTlsException("failed to load certificate from $path", e)
      }
    }

    /**
     * Loads a list of X.509 certificates from a PEM file.
     *
     * @param path path to the PEM-encoded certificate chain file
     * @return the list of X.509 certificates in the chain
     */
    @JvmStatic
    @Throws(OakSessionTlsException::class)
    fun loadCertificateChainFromFile(path: String): List<X509Certificate> {
      try {
        val cf = CertificateFactory.getInstance("X.509")
        return FileInputStream(path).use { fis ->
          cf.generateCertificates(fis).map { it as X509Certificate }
        }
      } catch (e: Exception) {
        throw OakSessionTlsException("failed to load certificate chain from $path", e)
      }
    }

    /**
     * Creates a [TlsIdentityProvider] from PEM key and certificate files.
     *
     * The provider always returns the same identity loaded from the specified files.
     */
    @JvmStatic
    @Throws(OakSessionTlsException::class)
    fun createIdentityProviderFromFiles(keyPath: String, certPath: String): TlsIdentityProvider {
      val identity =
        TlsIdentity(
          loadPrivateKeyFromFile(keyPath),
          loadCertificateChainFromFile(certPath).map { it.encoded },
        )
      return TlsIdentityProvider { identity }
    }

    /** Creates a [TrustAnchorProvider] that always returns the provided static certificate. */
    @JvmStatic
    fun createStaticTrustAnchorProvider(certDer: ByteArray): TrustAnchorProvider {
      return TrustAnchorProvider { certDer }
    }

    /** Creates a [TrustAnchorProvider] that loads a PEM certificate from a file path. */
    @JvmStatic
    @Throws(OakSessionTlsException::class)
    fun createTrustAnchorProviderFromFile(path: String): TrustAnchorProvider {
      val certDer = loadCertificateFromFile(path)
      return TrustAnchorProvider { certDer }
    }
  }
}

class OakSessionClientTlsContext(private val config: Config) : OakSessionTlsContext {

  class Config
  private constructor(
    val serverTrustAnchorProvider: TrustAnchorProvider? = null,
    val tlsIdentityProvider: TlsIdentityProvider? = null,
    val customCertVerifier: CustomCertVerifier? = null,
    val expectedServerName: String? = null,
    val provider: java.security.Provider? = null,
    val keyStoreType: String = KeyStore.getDefaultType(),
  ) {
    class Builder internal constructor() {
      private var serverTrustAnchorProvider: TrustAnchorProvider? = null
      private var tlsIdentityProvider: TlsIdentityProvider? = null
      private var customCertVerifier: CustomCertVerifier? = null
      private var expectedServerName: String? = null
      private var provider: java.security.Provider? = null
      private var keyStoreType: String = KeyStore.getDefaultType()

      /** Sets the trust anchor provider for server certificate verification. */
      fun serverTrustAnchorProvider(provider: TrustAnchorProvider) = apply {
        this.serverTrustAnchorProvider = provider
      }

      /** Sets the identity provider for client authentication (mTLS). */
      fun tlsIdentityProvider(provider: TlsIdentityProvider) = apply {
        this.tlsIdentityProvider = provider
      }

      /** Sets a custom certificate verifier for server certificates. */
      fun customCertVerifier(verifier: CustomCertVerifier) = apply {
        this.customCertVerifier = verifier
      }

      /** Sets the expected server identity for SNI and hostname verification. */
      fun expectedServerName(name: String) = apply { this.expectedServerName = name }

      /** Sets the security provider (e.g. Conscrypt) for standard JSSE. */
      fun provider(provider: java.security.Provider) = apply { this.provider = provider }

      /** Sets the KeyStore type to use for JSSE key/trust managers. */
      fun keyStoreType(type: String) = apply { this.keyStoreType = type }

      /** Builds the configuration. */
      fun build() =
        Config(
          serverTrustAnchorProvider,
          tlsIdentityProvider,
          customCertVerifier,
          expectedServerName,
          provider,
          keyStoreType,
        )
    }

    companion object {
      /** Creates a new builder. */
      @JvmStatic fun builder() = Builder()
    }
  }

  @Throws(OakSessionTlsException::class)
  override suspend fun newInitializedSession(
    send: SendFunction,
    receive: ReceiveFunction,
  ): OakSessionTlsInitializer.InitializedSession {
    val initializer = newSession()

    // Client sends initial frame (ClientHello) before entering the loop.
    val outgoing = initializer.getTLSFrame()
    if (outgoing.isNotEmpty()) send.send(outgoing)

    // Unified loop: receive, process, send response.
    while (!initializer.isReady) {
      val incoming = receive.receive()
      initializer.putTLSFrame(incoming)

      if (!initializer.isReady) {
        val outgoing = initializer.getTLSFrame()
        if (outgoing.isNotEmpty()) send.send(outgoing)
      }
    }

    // Drain any final outgoing frame.
    val finalFrame = initializer.getTLSFrame()
    if (finalFrame.isNotEmpty()) send.send(finalFrame)

    return initializer.getOpenSession()
  }

  @Throws(OakSessionTlsException::class)
  override fun newSession(): OakSessionTlsInitializer {
    try {
      val keyManagers: Array<KeyManager>? =
        config.tlsIdentityProvider?.let {
          arrayOf(createKeyManager(it.getIdentity(), config.keyStoreType))
        }

      val trustManagers =
        buildTrustManagers(
          config.serverTrustAnchorProvider?.getTrustAnchor(),
          config.customCertVerifier,
          config.keyStoreType,
        )

      // Create a fresh SSLContext per session so each gets the latest identity.
      val ctx =
        if (config.provider != null) {
          SSLContext.getInstance("TLSv1.3", config.provider)
        } else {
          SSLContext.getInstance("TLSv1.3")
        }
      ctx.init(keyManagers, trustManagers, null)

      val expected = config.expectedServerName ?: "oak-session-tls"
      val engine =
        ctx.createSSLEngine(expected, 0).apply {
          val params = sslParameters
          params.serverNames = listOf(javax.net.ssl.SNIHostName(expected))
          params.endpointIdentificationAlgorithm = "HTTPS"
          sslParameters = params
        }

      engine.useClientMode = true
      engine.enabledProtocols = arrayOf("TLSv1.3")
      engine.beginHandshake()

      return OakSessionTlsInitializer(engine)
    } catch (e: OakSessionTlsException) {
      throw e
    } catch (e: Exception) {
      throw OakSessionTlsException("failed to create TLS session", e)
    }
  }
}

class OakSessionServerTlsContext(private val config: Config) : OakSessionTlsContext {

  class Config
  private constructor(
    val tlsIdentityProvider: TlsIdentityProvider,
    val clientTrustAnchorProvider: TrustAnchorProvider? = null,
    val customCertVerifier: CustomCertVerifier? = null,
    val provider: java.security.Provider? = null,
    val keyStoreType: String = KeyStore.getDefaultType(),
  ) {
    class Builder internal constructor(private val tlsIdentityProvider: TlsIdentityProvider) {
      private var clientTrustAnchorProvider: TrustAnchorProvider? = null
      private var customCertVerifier: CustomCertVerifier? = null
      private var provider: java.security.Provider? = null
      private var keyStoreType: String = KeyStore.getDefaultType()

      /** Sets the trust anchor provider for client certificate verification. Enables mTLS. */
      fun clientTrustAnchorProvider(provider: TrustAnchorProvider) = apply {
        this.clientTrustAnchorProvider = provider
      }

      /** Sets a custom certificate verifier for client certificates. */
      fun customCertVerifier(verifier: CustomCertVerifier) = apply {
        this.customCertVerifier = verifier
      }

      /** Sets the security provider (e.g. Conscrypt) for standard JSSE. */
      fun provider(provider: java.security.Provider) = apply { this.provider = provider }

      /** Sets the KeyStore type to use for JSSE key/trust managers. */
      fun keyStoreType(type: String) = apply { this.keyStoreType = type }

      /** Builds the configuration. */
      fun build() =
        Config(
          tlsIdentityProvider,
          clientTrustAnchorProvider,
          customCertVerifier,
          provider,
          keyStoreType,
        )
    }

    companion object {
      /** Creates a new builder with the required identity provider. */
      @JvmStatic
      fun builder(tlsIdentityProvider: TlsIdentityProvider) = Builder(tlsIdentityProvider)
    }
  }

  @Throws(OakSessionTlsException::class)
  override suspend fun newInitializedSession(
    send: SendFunction,
    receive: ReceiveFunction,
  ): OakSessionTlsInitializer.InitializedSession {
    val initializer = newSession()

    // Unified loop: receive, process, send response.
    while (!initializer.isReady) {
      val incoming = receive.receive()
      initializer.putTLSFrame(incoming)

      if (!initializer.isReady) {
        val outgoing = initializer.getTLSFrame()
        if (outgoing.isNotEmpty()) send.send(outgoing)
      }
    }

    // Drain any final outgoing frame.
    val finalFrame = initializer.getTLSFrame()
    if (finalFrame.isNotEmpty()) send.send(finalFrame)

    return initializer.getOpenSession()
  }

  @Throws(OakSessionTlsException::class)
  override fun newSession(): OakSessionTlsInitializer {
    try {
      val keyManagers: Array<KeyManager>? =
        arrayOf(createKeyManager(config.tlsIdentityProvider.getIdentity(), config.keyStoreType))

      val trustManagers =
        buildTrustManagers(
          config.clientTrustAnchorProvider?.getTrustAnchor(),
          config.customCertVerifier,
          config.keyStoreType,
        )

      // Create a fresh SSLContext per session so each gets the latest identity.
      val ctx =
        if (config.provider != null) {
          SSLContext.getInstance("TLSv1.3", config.provider)
        } else {
          SSLContext.getInstance("TLSv1.3")
        }
      ctx.init(keyManagers, trustManagers, null)

      val engine = ctx.createSSLEngine()
      engine.useClientMode = false

      val requireClientAuth =
        config.clientTrustAnchorProvider != null || config.customCertVerifier != null
      if (requireClientAuth) {
        engine.needClientAuth = true
      }

      engine.enabledProtocols = arrayOf("TLSv1.3")
      engine.beginHandshake()

      return OakSessionTlsInitializer(engine)
    } catch (e: OakSessionTlsException) {
      throw e
    } catch (e: Exception) {
      throw OakSessionTlsException("failed to create TLS session", e)
    }
  }
}

/**
 * Custom trust manager that handles Conscrypt's "GENERIC" auth type and optionally delegates to a
 * custom verifier.
 *
 * Conscrypt uses "GENERIC" as the auth type for TLS 1.3 handshakes, which standard JDK trust
 * managers do not recognize. This wrapper normalizes the auth type before delegating.
 */
private class OakTrustManager(
  private val baseTrustManager: X509TrustManager?,
  private val customVerifier: CustomCertVerifier?,
) : X509ExtendedTrustManager() {

  override fun checkClientTrusted(chain: Array<X509Certificate>, authType: String) =
    doVerify(chain, authType, isClient = true)

  override fun checkServerTrusted(chain: Array<X509Certificate>, authType: String) =
    doVerify(chain, authType, isClient = false)

  override fun checkClientTrusted(chain: Array<X509Certificate>, authType: String, socket: Socket) =
    doVerify(chain, authType, isClient = true, socket = socket)

  override fun checkServerTrusted(chain: Array<X509Certificate>, authType: String, socket: Socket) =
    doVerify(chain, authType, isClient = false, socket = socket)

  override fun checkClientTrusted(
    chain: Array<X509Certificate>,
    authType: String,
    engine: SSLEngine,
  ) = doVerify(chain, authType, isClient = true, engine = engine)

  override fun checkServerTrusted(
    chain: Array<X509Certificate>,
    authType: String,
    engine: SSLEngine,
  ) = doVerify(chain, authType, isClient = false, engine = engine)

  override fun getAcceptedIssuers(): Array<X509Certificate> =
    baseTrustManager?.acceptedIssuers ?: emptyArray()

  @Throws(CertificateException::class)
  private fun doVerify(
    chain: Array<X509Certificate>,
    authType: String,
    isClient: Boolean,
    socket: Socket? = null,
    engine: SSLEngine? = null,
  ) {
    val normalizedAuthType = normalizeAuthType(authType, chain)

    // Run standard verification.
    var standardResult: CertificateException? = null
    if (baseTrustManager != null) {
      try {
        if (baseTrustManager is X509ExtendedTrustManager) {
          when {
            engine != null -> {
              if (isClient) {
                baseTrustManager.checkClientTrusted(chain, normalizedAuthType, engine)
              } else {
                baseTrustManager.checkServerTrusted(chain, normalizedAuthType, engine)
              }
            }
            socket != null -> {
              if (isClient) {
                baseTrustManager.checkClientTrusted(chain, normalizedAuthType, socket)
              } else {
                baseTrustManager.checkServerTrusted(chain, normalizedAuthType, socket)
              }
            }
            else -> {
              if (isClient) {
                baseTrustManager.checkClientTrusted(chain, normalizedAuthType)
              } else {
                baseTrustManager.checkServerTrusted(chain, normalizedAuthType)
              }
            }
          }
        } else {
          if (isClient) {
            baseTrustManager.checkClientTrusted(chain, normalizedAuthType)
          } else {
            baseTrustManager.checkServerTrusted(chain, normalizedAuthType)
          }
        }
      } catch (e: CertificateException) {
        standardResult = e
      }
    } else {
      standardResult = CertificateException("standard verification is not available")
    }

    if (customVerifier != null) {
      val derChain = chain.map { it.encoded }
      customVerifier.verify(derChain, standardResult)
    } else if (standardResult != null) {
      throw standardResult
    }
  }

  /**
   * Normalizes Conscrypt's "GENERIC" auth type to a recognized JDK auth type by inspecting the leaf
   * certificate's public key algorithm.
   */
  private fun normalizeAuthType(authType: String, chain: Array<X509Certificate>): String {
    if (authType != "GENERIC" || chain.isEmpty()) return authType

    return when (chain[0].publicKey.algorithm) {
      "EC" -> "ECDHE_ECDSA"
      "RSA" -> "RSA"
      "EdDSA",
      "Ed25519" -> "EDDSA"
      else -> authType
    }
  }
}

/**
 * Builds trust managers from an optional trust anchor certificate and optional custom verifier.
 *
 * Always wraps in [OakTrustManager] to handle Conscrypt's "GENERIC" auth type (used for TLS 1.3)
 * which standard JDK trust managers don't recognize.
 */
private fun buildTrustManagers(
  trustAnchorDer: ByteArray?,
  customVerifier: CustomCertVerifier?,
  keyStoreType: String,
): Array<TrustManager>? {
  if (trustAnchorDer == null && customVerifier == null) return null

  val baseTrustManager = trustAnchorDer?.let { loadTrustManager(it, keyStoreType) }
  return arrayOf(OakTrustManager(baseTrustManager, customVerifier))
}

/** Loads a trust manager from a DER-encoded certificate. */
private fun loadTrustManager(certDer: ByteArray, keyStoreType: String): X509TrustManager {
  val cf = CertificateFactory.getInstance("X.509")
  val trustStore = KeyStore.getInstance(keyStoreType)
  trustStore.load(null, null)

  cf.generateCertificates(ByteArrayInputStream(certDer)).forEachIndexed { index, cert ->
    trustStore.setCertificateEntry("trust-anchor-$index", cert)
  }

  val tmf = TrustManagerFactory.getInstance(TrustManagerFactory.getDefaultAlgorithm())
  tmf.init(trustStore)

  return tmf.trustManagers.filterIsInstance<X509TrustManager>().firstOrNull()
    ?: throw OakSessionTlsException("no X509TrustManager found")
}

/** Creates a KeyManager from a TlsIdentity (DER-encoded key and cert chain). */
private fun createKeyManager(identity: TlsIdentity, keyStoreType: String): X509ExtendedKeyManager {
  val keySpec = PKCS8EncodedKeySpec(identity.keyDer)

  // Try EC first, then RSA.
  val privateKey =
    runCatching { KeyFactory.getInstance("EC").generatePrivate(keySpec) }.getOrNull()
      ?: runCatching { KeyFactory.getInstance("RSA").generatePrivate(keySpec) }.getOrNull()
      ?: throw OakSessionTlsException("failed to parse private key (tried EC and RSA)")

  val cf = CertificateFactory.getInstance("X.509")
  val chain =
    identity.certChainDer
      .map { certDer -> cf.generateCertificate(ByteArrayInputStream(certDer)) as X509Certificate }
      .toTypedArray()

  val ks = KeyStore.getInstance(keyStoreType)
  ks.load(null, null)
  ks.setKeyEntry("identity", privateKey, charArrayOf(), chain)

  val kmf = KeyManagerFactory.getInstance(KeyManagerFactory.getDefaultAlgorithm())
  kmf.init(ks, charArrayOf())

  return kmf.keyManagers.filterIsInstance<X509ExtendedKeyManager>().firstOrNull()
    ?: throw OakSessionTlsException("no X509ExtendedKeyManager found")
}

/**
 * Provider interface that returns a [TlsIdentity].
 *
 * Called each time a new session is created on an [OakSessionTlsContext], enabling dynamic key
 * rotation without recreating the context.
 *
 * Implementations must be thread-safe if the context is shared across threads.
 */
fun interface TlsIdentityProvider {
  /**
   * Returns the current TLS identity (private key and certificate).
   *
   * @throws OakSessionTlsException if the identity cannot be retrieved
   */
  @Throws(OakSessionTlsException::class) fun getIdentity(): TlsIdentity
}

/**
 * Provider interface that returns a trust anchor certificate (DER-encoded).
 *
 * Called each time a new session is created on the context.
 */
fun interface TrustAnchorProvider {
  /**
   * Returns the DER-encoded trust anchor certificate.
   *
   * @throws OakSessionTlsException if the trust anchor cannot be retrieved
   */
  @Throws(OakSessionTlsException::class) fun getTrustAnchor(): ByteArray
}

/**
 * Custom certificate verification callback.
 *
 * Called during the TLS handshake with the full DER-encoded certificate chain and the result of
 * standard PKIX verification. This allows implementations to:
 * - Add additional checks after successful standard verification (e.g., DICE attestation)
 * - Override standard verification failures (e.g., accepting self-signed certificates verified via
 *   attestation evidence embedded in X.509 extensions)
 *
 * Mirrors the C++ `CustomCertVerifier` callback.
 */
fun interface CustomCertVerifier {
  /**
   * Verifies a certificate chain.
   *
   * @param certChainDer the full certificate chain, each element DER-encoded X.509
   * @param standardResult the exception from standard PKIX verification, or `null` if standard
   *   verification succeeded
   * @throws CertificateException if the certificate should be rejected. If this method returns
   *   normally, the certificate is accepted regardless of the standard verification result.
   */
  @Throws(CertificateException::class)
  fun verify(certChainDer: List<ByteArray>, standardResult: CertificateException?)
}

/**
 * Immutable holder for a TLS identity consisting of a private key and certificate chain.
 *
 * All values are DER-encoded: the private key in PKCS#8 format and each certificate in the chain in
 * X.509 format. This matches the C++ `TlsIdentity` struct which uses ASN.1/DER encoding.
 *
 * @property keyDer DER-encoded private key (PKCS#8 format)
 * @property certChainDer list of DER-encoded X.509 certificates in the chain
 */
class TlsIdentity(keyDer: ByteArray, certChainDer: List<ByteArray>) {
  private val _keyDer: ByteArray
  private val _certChainDer: List<ByteArray>

  init {
    require(keyDer.isNotEmpty()) { "keyDer must not be empty" }
    require(certChainDer.isNotEmpty()) { "certChainDer must not be empty" }
    for (cert in certChainDer) {
      require(cert.isNotEmpty()) { "certChainDer must not contain empty certificates" }
    }
    _keyDer = keyDer.copyOf()
    _certChainDer = certChainDer.map { it.copyOf() }
  }

  /** Returns a copy of the DER-encoded private key (PKCS#8). */
  val keyDer: ByteArray
    get() = _keyDer.copyOf()

  /** Returns copies of the DER-encoded X.509 certificates in the chain. */
  val certChainDer: List<ByteArray>
    get() = _certChainDer.map { it.copyOf() }
}
