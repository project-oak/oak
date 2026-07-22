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

import com.google.oak.util.FileUtil
import java.nio.ByteBuffer
import java.security.cert.CertificateException
import java.util.concurrent.ArrayBlockingQueue
import kotlin.test.assertNotNull
import kotlin.test.assertTrue
import kotlin.test.fail
import kotlinx.coroutines.runBlocking
import org.junit.Assert.assertArrayEquals
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

/** Tests for the Kotlin Oak Session TLS library, mirroring the C++ test suite. */
@RunWith(JUnit4::class)
class OakSessionTlsTest {

  // -- Tests --

  @Test
  fun testManualHandshake() {
    val serverProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_SERVER_KEY_PATH,
        TEST_SERVER_CERT_PATH,
      )
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .build()
      )

    val serverInit = serverCtx.newSession()
    val clientInit = clientCtx.newSession()

    // Client sends ClientHello.
    var clientFrame = clientInit.getTLSFrame()
    assertTrue(clientFrame.isNotEmpty(), "ClientHello should not be empty")

    // Drive the handshake in a loop.
    for (i in 0 until 10) {
      if (clientInit.isReady && serverInit.isReady) break

      if (clientFrame.isNotEmpty()) serverInit.putTLSFrame(clientFrame)
      val serverFrame = serverInit.getTLSFrame()
      if (serverFrame.isNotEmpty()) clientInit.putTLSFrame(serverFrame)
      clientFrame = clientInit.getTLSFrame()
    }

    assertTrue(clientInit.isReady, "client should be ready after handshake loop")

    val clientResult = clientInit.getOpenSession()
    assertNotNull(clientResult.session)

    // Server might still need client's Finished.
    if (!serverInit.isReady && clientFrame.isNotEmpty()) {
      serverInit.putTLSFrame(clientFrame)
    }
    assertTrue(serverInit.isReady, "server should be ready after handshake loop")

    val serverResult = serverInit.getOpenSession()
    assertNotNull(serverResult.session)

    // Verify bidirectional communication.
    sendReceiveAndVerify(serverResult.session, clientResult.session, "hello client".toByteArray())
    sendReceiveAndVerify(
      clientResult.session,
      serverResult.session,
      "hello again server".toByteArray(),
    )
  }

  @Test
  fun testNewInitializedSession() {
    val serverProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_SERVER_KEY_PATH,
        TEST_SERVER_CERT_PATH,
      )
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    result.clientError?.let { fail("client error: ${it.message}") }
    result.serverError?.let { fail("server error: ${it.message}") }
    assertNotNull(result.client, "client handshake should succeed")
    assertNotNull(result.server, "server handshake should succeed")

    sendReceiveAndVerify(
      result.client!!.session,
      result.server!!.session,
      "hello from client".toByteArray(),
    )
    sendReceiveAndVerify(
      result.server!!.session,
      result.client!!.session,
      "hello from server".toByteArray(),
    )
  }

  @Test
  fun testUntrustedCertificateRejected() {
    val serverProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_UNTRUSTED_KEY_PATH,
        TEST_UNTRUSTED_CERT_PATH,
      )
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    assertTrue(
      result.clientError != null || result.serverError != null,
      "handshake should fail with untrusted cert",
    )
  }

  @Test
  fun testCustomCertVerifierSuccess() {
    val serverProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_SERVER_KEY_PATH,
        TEST_SERVER_CERT_PATH,
      )
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())

    var verifierCalled = false
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .customCertVerifier(
            CustomCertVerifier { chain, standardResult ->
              verifierCalled = true
              assertTrue(chain.isNotEmpty(), "chain should not be empty")
              standardResult?.let { throw it }
            }
          )
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    assertNotNull(result.client, "client handshake should succeed")
    assertNotNull(result.server, "server handshake should succeed")
    assertTrue(verifierCalled, "custom verifier should have been called")
  }

  @Test
  fun testCustomCertVerifierFailure() {
    val serverProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_SERVER_KEY_PATH,
        TEST_SERVER_CERT_PATH,
      )
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())

    var verifierCalled = false
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .customCertVerifier(
            CustomCertVerifier { _, _ ->
              verifierCalled = true
              throw CertificateException("custom logic rejected cert")
            }
          )
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    assertTrue(
      result.clientError != null || result.serverError != null,
      "handshake should fail when custom verifier rejects",
    )
    assertTrue(verifierCalled, "custom verifier should have been called")
  }

  @Test
  fun testCustomCertVerifierOverridesUntrusted() {
    val serverProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_UNTRUSTED_KEY_PATH,
        TEST_UNTRUSTED_CERT_PATH,
      )
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())

    var verifierCalled = false
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .customCertVerifier(
            CustomCertVerifier { _, standardResult ->
              verifierCalled = true
              assertNotNull(standardResult, "standard verification should fail for untrusted cert")
              // Override by returning normally.
            }
          )
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    assertTrue(verifierCalled, "custom verifier should have been called")
    result.clientError?.let { fail("client should succeed after custom override: ${it.message}") }
    assertNotNull(result.client, "client session should be initialized")
  }

  @Test
  fun testCertificateRotationWorks() {
    val serverKey = OakSessionTlsContext.loadPrivateKeyFromFile(TEST_SERVER_KEY_PATH)
    val serverCert = OakSessionTlsContext.loadCertificateFromFile(TEST_SERVER_CERT_PATH)
    val untrustedKey = OakSessionTlsContext.loadPrivateKeyFromFile(TEST_UNTRUSTED_KEY_PATH)
    val untrustedCert = OakSessionTlsContext.loadCertificateFromFile(TEST_UNTRUSTED_CERT_PATH)

    var currentIdentity = TlsIdentity(serverKey, listOf(serverCert))
    val rotatingProvider = TlsIdentityProvider { currentIdentity }

    val serverCtx =
      OakSessionTlsContext.create(
        OakSessionServerTlsContext.Config.builder(rotatingProvider).build()
      )

    // First session: trusted cert → should succeed.
    val clientCtx1 =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .build()
      )
    val result1 = runHandshake(clientCtx1, serverCtx)
    assertNotNull(result1.client, "first session should succeed")

    // Rotate to untrusted cert.
    currentIdentity = TlsIdentity(untrustedKey, listOf(untrustedCert))

    // Second session: untrusted cert → should fail.
    val clientCtx2 =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .build()
      )
    val result2 = runHandshake(clientCtx2, serverCtx)
    assertTrue(
      result2.clientError != null || result2.serverError != null,
      "second session should fail with rotated untrusted cert",
    )
  }

  @Test
  fun testMtlsSession() {
    val serverProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_SERVER_KEY_PATH,
        TEST_SERVER_CERT_PATH,
      )
    val serverCtx =
      OakSessionTlsContext.create(
        OakSessionServerTlsContext.Config.builder(serverProvider)
          .clientTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .build()
      )

    val clientProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_CLIENT_KEY_PATH,
        TEST_CLIENT_CERT_PATH,
      )
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .tlsIdentityProvider(clientProvider)
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    result.clientError?.let { fail("client error: ${it.message}") }
    result.serverError?.let { fail("server error: ${it.message}") }
    assertNotNull(result.client, "client should succeed")
    assertNotNull(result.server, "server should succeed")

    sendReceiveAndVerify(
      result.client!!.session,
      result.server!!.session,
      "hello from client".toByteArray(),
    )
    sendReceiveAndVerify(
      result.server!!.session,
      result.client!!.session,
      "hello from server".toByteArray(),
    )
  }

  @Test
  fun testLargeDataTransfer() {
    val serverProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_SERVER_KEY_PATH,
        TEST_SERVER_CERT_PATH,
      )
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    assertNotNull(result.client, "client should succeed")
    assertNotNull(result.server, "server should succeed")

    val largeMessage = createTestData(100_000)
    sendReceiveAndVerify(result.client!!.session, result.server!!.session, largeMessage)
  }

  @Test
  fun testCustomBuffer() {
    val serverProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_SERVER_KEY_PATH,
        TEST_SERVER_CERT_PATH,
      )
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    val client = result.client!!.session
    val server = result.server!!.session

    val message = "test message with custom buffers".toByteArray()

    val encryptBuffer = ByteBuffer.allocate(64 * 1024)
    val decryptBuffer = ByteBuffer.allocate(64 * 1024)

    val encBuf = client.encrypt(message, encryptBuffer)
    val encrypted = ByteArray(encBuf.remaining()).also { encBuf.get(it) }

    val decBuf = server.decrypt(encrypted, decryptBuffer)
    val decrypted = ByteArray(decBuf.remaining()).also { decBuf.get(it) }
    assertArrayEquals("decrypted message should match original", message, decrypted)

    // Verify capacity adjustment works on tinyBuffer
    val tinyBuffer = ByteBuffer.allocate(1)
    val adjustedEncBuf = client.encrypt(message, tinyBuffer)
    assertTrue(adjustedEncBuf !== tinyBuffer, "should have allocated a new buffer")
    assertTrue(adjustedEncBuf.capacity() > 1, "should have adjusted capacity")

    val encryptedFromTiny = ByteArray(adjustedEncBuf.remaining()).also { adjustedEncBuf.get(it) }

    val adjustedDecBuf = server.decrypt(encryptedFromTiny, tinyBuffer)
    assertTrue(adjustedDecBuf !== tinyBuffer, "should have allocated a new buffer")
    assertTrue(adjustedDecBuf.capacity() > 1, "should have adjusted capacity")

    val decryptedFromTiny = ByteArray(adjustedDecBuf.remaining()).also { adjustedDecBuf.get(it) }
    assertArrayEquals("decrypted message should match original", message, decryptedFromTiny)

    // Verify calling with null/omitted buffer allocates new buffer
    val defaultEncBuf = client.encrypt(message)
    val encryptedFromDefault = ByteArray(defaultEncBuf.remaining()).also { defaultEncBuf.get(it) }

    val defaultDecBuf = server.decrypt(encryptedFromDefault)
    val decryptedFromDefault = ByteArray(defaultDecBuf.remaining()).also { defaultDecBuf.get(it) }
    assertArrayEquals("decrypted message should match original", message, decryptedFromDefault)
  }

  @Test
  fun testCustomKeyStoreType() {
    val serverProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_SERVER_KEY_PATH,
        TEST_SERVER_CERT_PATH,
      )
    val serverCtx =
      OakSessionTlsContext.create(
        OakSessionServerTlsContext.Config.builder(serverProvider).keyStoreType("PKCS12").build()
      )
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .keyStoreType("PKCS12")
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    assertNotNull(result.client, "client should succeed")
    assertNotNull(result.server, "server should succeed")

    val message = "test message with PKCS12 keystore".toByteArray()
    sendReceiveAndVerify(result.client!!.session, result.server!!.session, message)
  }

  @Test
  fun testCreateSelfSignedNoExtensions() {
    val provider = CertUtil.createSelfSigned()
    val identity = provider.getIdentity()
    assertNotNull(identity.keyDer)
    assertTrue(identity.keyDer.isNotEmpty(), "key should not be empty")
    assertTrue(identity.certChainDer.isNotEmpty(), "cert chain should not be empty")
    assertTrue(identity.certChainDer[0].isNotEmpty(), "leaf cert should not be empty")
  }

  @Test
  fun testCreateSelfSignedWithExtension() {
    val testValue = "test-attestation-data".toByteArray()
    val extensions = listOf(X509Extension("1.2.3.4.5.6.7.8.9", testValue, false))

    val provider = CertUtil.createSelfSigned(extensions)
    val identity = provider.getIdentity()
    assertTrue(identity.keyDer.isNotEmpty(), "key should not be empty")
    assertTrue(identity.certChainDer.isNotEmpty(), "cert chain should not be empty")
    assertTrue(identity.certChainDer[0].isNotEmpty(), "leaf cert should not be empty")

    // Parse the certificate and verify the extension is present.
    val cf = java.security.cert.CertificateFactory.getInstance("X.509")
    val cert =
      cf.generateCertificate(java.io.ByteArrayInputStream(identity.certChainDer[0]))
        as java.security.cert.X509Certificate

    val extValue = cert.getExtensionValue("1.2.3.4.5.6.7.8.9")
    assertNotNull(extValue, "extension should be present in certificate")
  }

  @Test
  fun testSelfSignedHandshake() {
    val serverProvider = CertUtil.createSelfSigned()
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .customCertVerifier(CustomCertVerifier { _, _ -> /* accept any */ })
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    result.clientError?.let { fail("client error: ${it.message}") }
    result.serverError?.let { fail("server error: ${it.message}") }
    assertNotNull(result.client, "client should succeed")
    assertNotNull(result.server, "server should succeed")

    sendReceiveAndVerify(result.client!!.session, result.server!!.session, "hello".toByteArray())
  }

  @Test
  fun testHostnameVerificationSuccess() {
    val serverProvider = CertUtil.createSelfSigned(serverName = "my-custom-server")
    val identity = serverProvider.getIdentity()
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())

    val trustAnchor =
      OakSessionTlsContext.createStaticTrustAnchorsProvider(listOf(identity.certChainDer[0]))
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(trustAnchor)
          .expectedServerName("my-custom-server")
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    result.clientError?.let { fail("client error: ${it.message}") }
    result.serverError?.let { fail("server error: ${it.message}") }
    assertNotNull(result.client, "client should succeed")
  }

  @Test
  fun testHostnameVerificationFailure() {
    val serverProvider = CertUtil.createSelfSigned(serverName = "my-custom-server")
    val identity = serverProvider.getIdentity()
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())

    val trustAnchor =
      OakSessionTlsContext.createStaticTrustAnchorsProvider(listOf(identity.certChainDer[0]))
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(trustAnchor)
          .expectedServerName("mismatched-server-name")
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    assertTrue(
      result.clientError != null || result.serverError != null,
      "handshake should fail due to hostname mismatch",
    )
  }

  @Test
  fun testCustomCertVerifierGetsStandardErrorOnEmptyTrustAnchor() {
    val serverProvider = CertUtil.createSelfSigned()
    val serverCtx =
      OakSessionTlsContext.create(OakSessionServerTlsContext.Config.builder(serverProvider).build())

    var verifierCalled = false
    var receivedStandardError = false
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .customCertVerifier(
            CustomCertVerifier { _, standardResult ->
              verifierCalled = true
              if (standardResult != null) {
                receivedStandardError = true
              }
            }
          )
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    assertNotNull(result.client, "client should succeed")
    assertTrue(verifierCalled, "custom verifier should be called")
    assertTrue(
      receivedStandardError,
      "custom verifier should receive standardResult exception indicating standard verification is not available",
    )
  }

  @Test
  fun testExplicitProviderHandshake() {
    val provider = org.conscrypt.Conscrypt.newProvider()
    val serverProvider =
      OakSessionTlsContext.createIdentityProviderFromFiles(
        TEST_SERVER_KEY_PATH,
        TEST_SERVER_CERT_PATH,
      )
    val serverCtx =
      OakSessionTlsContext.create(
        OakSessionServerTlsContext.Config.builder(serverProvider).provider(provider).build()
      )
    val clientCtx =
      OakSessionTlsContext.create(
        OakSessionClientTlsContext.Config.builder()
          .serverTrustAnchorProvider(
            OakSessionTlsContext.createTrustAnchorProviderFromFile(TEST_CA_CERT_PATH)
          )
          .provider(provider)
          .build()
      )

    val result = runHandshake(clientCtx, serverCtx)
    result.clientError?.let { fail("client error: ${it.message}") }
    result.serverError?.let { fail("server error: ${it.message}") }
    assertNotNull(result.client, "client handshake should succeed")
    assertNotNull(result.server, "server handshake should succeed")

    sendReceiveAndVerify(
      result.client!!.session,
      result.server!!.session,
      "hello from client explicitly using provider".toByteArray(),
    )
  }

  // -- Helper methods --

  private data class HandshakeResult(
    var client: OakSessionTlsInitializer.InitializedSession? = null,
    var server: OakSessionTlsInitializer.InitializedSession? = null,
    var clientError: OakSessionTlsException? = null,
    var serverError: OakSessionTlsException? = null,
  )

  /** Runs the automatic handshake for both client and server concurrently. */
  private fun runHandshake(
    clientCtx: OakSessionTlsContext,
    serverCtx: OakSessionTlsContext,
  ): HandshakeResult {
    val clientToServer = ArrayBlockingQueue<ByteArray>(16)
    val serverToClient = ArrayBlockingQueue<ByteArray>(16)
    val result = HandshakeResult()

    val serverThread = Thread {
      try {
        result.server = runBlocking {
          serverCtx.newInitializedSession(
            { data -> serverToClient.put(data) },
            { clientToServer.take() },
          )
        }
      } catch (e: OakSessionTlsException) {
        result.serverError = e
      }
    }
    serverThread.start()

    try {
      result.client = runBlocking {
        clientCtx.newInitializedSession(
          { data -> clientToServer.put(data) },
          { serverToClient.take() },
        )
      }
    } catch (e: OakSessionTlsException) {
      result.clientError = e
    }

    serverThread.join(10_000)
    return result
  }

  /** Encrypts with sender, decrypts with receiver, verifies round-trip. */
  private fun sendReceiveAndVerify(
    sender: OakSessionTls,
    receiver: OakSessionTls,
    message: ByteArray,
  ) {
    val maxTlsPacketSize = 18 * 1024
    val estimatedRecords = (message.size / (16 * 1024)) + 2
    val encryptBuffer = ByteBuffer.allocate(estimatedRecords * maxTlsPacketSize)
    val decryptBuffer = ByteBuffer.allocate(maxOf(encryptBuffer.capacity(), 64 * 1024))

    val encBuf = sender.encrypt(message, encryptBuffer)
    val encrypted = ByteArray(encBuf.remaining()).also { encBuf.get(it) }
    assertTrue(encrypted.isNotEmpty(), "encrypted should not be empty")

    val decBuf = receiver.decrypt(encrypted, decryptBuffer)
    val decrypted = ByteArray(decBuf.remaining()).also { decBuf.get(it) }
    assertArrayEquals("decrypted message should match original", message, decrypted)
  }

  /** Creates test data of the specified size with predictable content. */
  private fun createTestData(size: Int) = ByteArray(size) { (it % 256).toByte() }

  companion object {
    init {
      java.security.Security.insertProviderAt(org.conscrypt.Conscrypt.newProvider(), 1)
    }

    private val TEST_SERVER_KEY_PATH =
      FileUtil.getRunfilePath("oak_session/tls/testing/test_server.key")
    private val TEST_SERVER_CERT_PATH =
      FileUtil.getRunfilePath("oak_session/tls/testing/test_server.pem")
    private val TEST_CLIENT_KEY_PATH =
      FileUtil.getRunfilePath("oak_session/tls/testing/test_client.key")
    private val TEST_CLIENT_CERT_PATH =
      FileUtil.getRunfilePath("oak_session/tls/testing/test_client.pem")
    private val TEST_CA_CERT_PATH = FileUtil.getRunfilePath("oak_session/tls/testing/test_ca.pem")
    private val TEST_UNTRUSTED_KEY_PATH =
      FileUtil.getRunfilePath("oak_session/tls/testing/test_untrusted.key")
    private val TEST_UNTRUSTED_CERT_PATH =
      FileUtil.getRunfilePath("oak_session/tls/testing/test_untrusted.pem")
  }
}
