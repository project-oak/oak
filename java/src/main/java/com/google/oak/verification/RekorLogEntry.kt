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
package com.google.oak.verification

import com.google.gson.Gson
import com.google.gson.GsonBuilder
import com.google.gson.JsonSyntaxException
import com.google.gson.reflect.TypeToken
import java.nio.charset.StandardCharsets
import java.util.Base64

/**
 * Provides structs for parsing Rekor log entries of `hashedrekord` type. See
 * <https://docs.rs/sigstore/latest/src/sigstore/rekor/models/hashedrekord.rs.html>
 */
data class RekorLogEntry(
  // package-private for testing
  val logEntry: LogEntry
) {
  // The following nested classes represent a subset of Rekor types defined in
  // <https://github.com/sigstore/rekor/tree/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models>.
  //
  // These classes are intentionally made package-private and immutable, as the
  // clients are not expected to instantiate them directly. The fields are not
  // explicitly made final to allow instantiation with Gson.
  data class LogEntry(
    /** We cannot directly use the type `Body` here, since body is Base64-encoded. */
    val body: String,

    /**
     * Unmarshaled body of this LogEntry. It is declared as a transient field, so that it is
     * excluded when serializing and deserializing instances of LogEntry.
     */
    val integratedTime: Long,

    /**
     * The SHA2-256 hash of the DER-encoded public key for the log at the time the entry was
     * included in the log. Pattern: ^[0-9a-fA-F]{64}$
     */
    val logID: String,

    /** Minimum: 0 */
    var logIndex: Long,
  ) {
    @kotlin.jvm.Transient var bodyObject: Body? = null

    /** Includes a signature over the body, integratedTime, logID, and logIndex. */
    internal var verification: LogEntryVerification? = null
  }

  /** Represents the body in a Rekor LogEntry. */
  data class Body(val apiVersion: String, val kind: String, val spec: Spec)

  /** Represents the `spec` in the body of a Rekor LogEntry. */
  data class Spec(val data: Data, val signature: GenericSignature)

  /** Represents the hashed data in the body of a Rekor LogEntry. */
  data class Data(val hash: Hash)

  /** Represents a hash digest. */
  data class Hash(val algorithm: String, val value: String)

  /** Represents a signature in the body of a Rekor LogEntry. */
  data class GenericSignature(
    /** Base64 content that is signed. */
    val content: String,

    /** Public key associated with the signing key that generated this signature. */
    val publicKey: PublicKey,
  )

  /** Represents a public key included in the body of a Rekor LogEntry. */
  data class PublicKey(
    /** Base64 content of a public key. */
    val content: String
  )

  /**
   * Represents a verification object in a Rekor LogEntry. The verification object in Rekor also
   * contains an inclusion proof. Since we currently don't verify the inclusion proof in the client,
   * it is omitted from this struct.
   *
   * Based on
   * <https:></https:>//github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/log_entry.go#L341>.
   */
  internal data class LogEntryVerification(
    /** Base64-encoded signature over the body, integratedTime, logID, and logIndex. */
    val signedEntryTimestamp: String
  )

  val body: Body?
    /** Returns the body of the log entry. */
    get() = logEntry.bodyObject

  fun hasVerification(): Boolean {
    return logEntry.verification != null
  }

  companion object {
    /**
     * Creates an instance from the given JSON string.
     *
     * @param json the input JSON string
     * @return the desired instance
     * @throws IllegalArgumentException whenever the creation fails
     */
    fun createFromJson(json: String): RekorLogEntry {
      // Use a default Gson instance to parse JSON strings into Java objects.
      val gson: Gson = GsonBuilder().create()
      val entryMap: Map<String, Any> =
        try {
          gson.fromJson(json, object : TypeToken<Map<String?, Any?>?>() {}.getType())
        } catch (e: JsonSyntaxException) {
          throw IllegalArgumentException(e)
        }

      require(entryMap.size == 1) {
        "Expected exactly one entry in the json-formatted Rekor log entry, found ${
            entryMap.size}"
      }
      val entryStr = gson.toJson(entryMap.values.iterator().next())
      val entry: LogEntry = gson.fromJson(entryStr, LogEntry::class.java)
      val decodedBody = String(Base64.getDecoder().decode(entry.body))
      entry.bodyObject = gson.fromJson(decodedBody, Body::class.java)
      return RekorLogEntry(entry)
    }

    /** Same as before, but passing a byte array. */
    fun createFromJson(json: ByteArray): RekorLogEntry {
      return createFromJson(String(json, StandardCharsets.UTF_8))
    }
  }
}
