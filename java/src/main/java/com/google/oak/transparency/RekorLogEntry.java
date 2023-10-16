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

package com.google.oak.transparency;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.reflect.TypeToken;
import java.nio.charset.StandardCharsets;
import java.util.Base64;
import java.util.Map;

/**
 * Represents a Rekor LogEntry as defined in
 * https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/log_entry.go#L89
 */
public final class RekorLogEntry {
  // The following nested classes represent a subset of Rekor types defined in
  // <https://github.com/sigstore/rekor/tree/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models>.
  //
  // These classes are intentionally made package-private and immutable, as the
  // clients are not expected to instantiate them directly. The fields are not
  // explicitly made final to allow instantiation with Gson.

  static class LogEntry {
    /**
     * We cannot directly use the type `Body` here, since body is Base64-encoded.
     */
    String body;

    /**
     * Unmarshaled body of this LogEntry. It is declared as a transient field, so
     * that it is excluded when serializing and deserializing instances of LogEntry.
     */
    transient Body bodyObject;

    long integratedTime;

    /**
     * The SHA2-256 hash of the DER-encoded public key for the log at the time
     * the entry was included in the log. Pattern: ^[0-9a-fA-F]{64}$
     */
    String logID;

    /** Minimum: 0 */
    long logIndex;

    /** Includes a signature over the body, integratedTime, logID, and logIndex. */
    LogEntryVerification verification;
  }

  /**
   * Represents the body in a Rekor LogEntry.
   *
   * <p>
   * Based on
   * <https://github.com/sigstore/rekor/blob/fc913fe7800ea5faed1c4900d8a6ffe11eb7be32/pkg/generated/models/rekord.go#L38>.
   * Note that `kind` is a derived field.
   */
  static class Body {
    String apiVersion;
    String kind;
    Spec spec;
  }

  /**
   * Represents the `spec` in the body of a Rekor LogEntry.
   *
   * <p>
   * Based on
   * <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L39.>
   */
  static class Spec {
    Data data;
    GenericSignature signature;
  }

  /**
   * Represents the hashed data in the body of a Rekor LogEntry.
   *
   * <p>
   * Based on
   * <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L179.>
   */
  static class Data { Hash hash; }

  /**
   * Represents a hash digest.
   *
   * <p>
   * Based on
   * <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L273.>
   */
  static class Hash {
    String algorithm;
    String value;
  }

  /**
   * Represents a signature in the body of a Rekor LogEntry.
   *
   * <p>
   * Based on
   * <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L383>
   */
  static class GenericSignature {
    /** Base64 content that is signed. */
    String content;

    /** Signature format, e.g., x509. */
    String format;

    /** Public key associated with the signing key that generated this signature. */
    PublicKey publicKey;
  }

  /**
   * Represents a public key included in the body of a Rekor LogEntry.
   *
   * <p>
   * Based on
   * <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/rekord_v001_schema.go#L551.>
   */
  static class PublicKey {
    /** Base64 content of a public key. */
    String content;
  }

  /**
   * Represents a verification object in a Rekor LogEntry. The verification object
   * in Rekor also contains an inclusion proof. Since we currently don't verify
   * the inclusion proof in the client, it is omitted from this struct.
   *
   * <p>
   * Based on
   * <https://github.com/sigstore/rekor/blob/2978cdc26fdf8f5bfede8459afd9735f0f231a2a/pkg/generated/models/log_entry.go#L341>.
   */
  static class LogEntryVerification {
    /**
     * Base64-encoded signature over the body, integratedTime, logID, and logIndex.
     */
    String signedEntryTimestamp;
  }

  /**
   * Creates an instance from the given JSON string.
   *
   * @param json the input JSON string
   * @return the desired instance
   * @throws IllegalArgumentException whenever the creation fails
   */
  public static RekorLogEntry createFromJson(String json) {
    // Use a default Gson instance to parse JSON strings into Java objects.
    Gson gson = new GsonBuilder().create();
    Map<String, Object> entryMap =
        gson.fromJson(json, new TypeToken<Map<String, Object>>() {}.getType());

    if (entryMap.size() != 1) {
      throw new IllegalArgumentException(
          "Expected exactly one entry in the json-formatted Rekor log entry, found "
          + entryMap.size());
    }

    String entryStr = gson.toJson(entryMap.values().iterator().next());
    LogEntry entry = gson.fromJson(entryStr, LogEntry.class);
    String decodedBody = new String(Base64.getDecoder().decode(entry.body));
    entry.bodyObject = gson.fromJson(decodedBody, Body.class);
    return new RekorLogEntry(entry);
  }

  /** Same as before, but passing a byte array. */
  public static RekorLogEntry createFromJson(byte[] json) {
    return createFromJson(new String(json, StandardCharsets.UTF_8));
  }

  final LogEntry logEntry; // package-private for testing

  private RekorLogEntry(LogEntry logEntry) {
    this.logEntry = logEntry;
  }

  /** Returns the body of the log entry. */
  public Body getBody() {
    return logEntry.bodyObject;
  }

  public boolean hasVerification() {
    return logEntry.verification != null;
  }
}
