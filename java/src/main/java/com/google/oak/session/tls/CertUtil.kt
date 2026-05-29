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

import java.math.BigInteger
import java.security.KeyPair
import java.security.KeyPairGenerator
import java.security.spec.ECGenParameterSpec
import java.util.Date
import org.bouncycastle.asn1.ASN1ObjectIdentifier
import org.bouncycastle.asn1.DEROctetString
import org.bouncycastle.asn1.x500.X500Name
import org.bouncycastle.asn1.x509.BasicConstraints
import org.bouncycastle.asn1.x509.Extension
import org.bouncycastle.asn1.x509.GeneralName
import org.bouncycastle.asn1.x509.GeneralNames
import org.bouncycastle.cert.jcajce.JcaX509v3CertificateBuilder
import org.bouncycastle.operator.jcajce.JcaContentSignerBuilder

/** Utility methods for generating self-signed identity providers. */
object CertUtil {

  /**
   * Creates a self-signed [TlsIdentityProvider] with optional X.509 extensions and an optional
   * server name.
   *
   * Generates a new EC P-256 key pair and a self-signed certificate.
   *
   * @param extensions optional X.509v3 extensions to embed in the certificate
   * @param serverName the expected server name to embed in the Common Name and DNS SAN (defaults to
   *   "oak-session-tls")
   */
  @JvmStatic
  @JvmOverloads
  @Throws(OakSessionTlsException::class)
  fun createSelfSigned(
    extensions: List<X509Extension> = emptyList(),
    serverName: String = "oak-session-tls",
  ): TlsIdentityProvider {
    try {
      val kpg = KeyPairGenerator.getInstance("EC")
      kpg.initialize(ECGenParameterSpec("secp256r1"))
      val keyPair = kpg.generateKeyPair()

      val certDer = buildSelfSignedCert(keyPair, serverName, extensions)
      val keyDer = keyPair.private.encoded // PKCS#8

      val identity = TlsIdentity(keyDer, listOf(certDer))
      return TlsIdentityProvider { identity }
    } catch (e: Exception) {
      throw OakSessionTlsException("failed to create self-signed identity", e)
    }
  }

  /** Builds a self-signed X.509 certificate using Bouncy Castle. */
  private fun buildSelfSignedCert(
    keyPair: KeyPair,
    serverName: String,
    extensions: List<X509Extension>,
  ): ByteArray {
    val owner = X500Name("CN=$serverName, O=Oak")
    val serial = BigInteger.valueOf(System.currentTimeMillis())
    val notBefore = Date()
    val notAfter = Date(notBefore.time + 365L * 24 * 60 * 60 * 1000) // 1 year

    val certBuilder =
      JcaX509v3CertificateBuilder(owner, serial, notBefore, notAfter, owner, keyPair.public)

    // Basic Constraints (non-CA)
    certBuilder.addExtension(Extension.basicConstraints, true, BasicConstraints(false))

    // Subject Alternative Name (SAN) DNS entry
    if (serverName.isNotEmpty()) {
      val generalName = GeneralName(GeneralName.dNSName, serverName)
      val generalNames = GeneralNames(generalName)
      certBuilder.addExtension(Extension.subjectAlternativeName, false, generalNames)
    }

    // Custom extensions
    for (ext in extensions) {
      val extOid = ASN1ObjectIdentifier(ext.oid)
      val value = DEROctetString(ext.value)
      certBuilder.addExtension(extOid, ext.critical, value)
    }

    val signer = JcaContentSignerBuilder("SHA256withECDSA").build(keyPair.private)
    val holder = certBuilder.build(signer)
    return holder.encoded
  }
}

/**
 * Immutable holder for an X.509v3 extension.
 *
 * Extensions are identified by an OID and contain a DER-encoded value. Use this with
 * [CertUtil.createSelfSigned] to embed application-specific data (e.g., attestation evidence) in
 * the certificate.
 *
 * @property oid the OID in dotted-decimal notation (e.g., "1.2.3.4.5")
 * @property value the extension value bytes
 * @property critical whether this extension is critical
 */
class X509Extension(val oid: String, value: ByteArray, val critical: Boolean) {
  private val _value: ByteArray = value.copyOf()

  init {
    require(oid.isNotEmpty()) { "oid must not be empty" }
  }

  /** Returns a copy of the extension value. */
  val value: ByteArray
    get() = _value.copyOf()
}
