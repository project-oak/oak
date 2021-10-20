//
// Copyright 2021 The Project Oak Authors
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

package com.google.oak.functions.client;

import com.google.common.hash.Hashing;
import com.google.oak.remote_attestation.Message.ServerIdentity;
import com.google.protobuf.InvalidProtocolBufferException;
import java.nio.ByteBuffer;
import java.util.Arrays;
import java.util.function.Predicate;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.functions.abi.ConfigurationInfo;
import oak.remote_attestation.AttestationInfo;
import oak.remote_attestation.AttestationReport;

/**
 * A verifier that verifies an instance of {@code ServerIdentity}. The verification involves
 * verifying the attestation report, and the server {@code ConfigurationInfo} based on a given
 * predicate.
 */
public class ServerIdentityVerifier {
  private static final Logger logger = Logger.getLogger(ServerIdentityVerifier.class.getName());
  private final ServerIdentity serverIdentity;
  private final Predicate<ConfigurationInfo> configurationVerifier;

  public ServerIdentityVerifier(
      ServerIdentity serverIdentity, Predicate<ConfigurationInfo> configurationVerifier) {
    this.serverIdentity = serverIdentity;
    this.configurationVerifier = configurationVerifier;
  }

  /**
   * Verifies the encapsulated ServerIdentity, by calling {@code
   * ServerIdentityVerifier::verifyConfigurationInfo} and {@code
   * ServerIdentityVerifier::verifyAttestationInfo}.
   * @return
   */
  public boolean verify() {
    return verifyConfigurationInfo() && verifyAttestationInfo();
  }

  /**
   * Verifies the {@code ConfigurationInfo} in the {@code serverIdentity}.
   *
   * The `additionalInfo` field of {@code serverIdentity} is expected to contain an instance of
   * {@code ConfigurationInfo} as a binary-encoded protobuf message. This byte array is parsed
   * into an instance of {@code ConfigurationInfo}. Returns false if parsing fails. Otherwise tests
   * the {@code configurationVerifier} predicate for the resulting {@code ConfigurationInfo}, and
   * returns the result.
   *
   * @return the result of calling test {@code configurationVerifier} as described above.
   */
  boolean verifyConfigurationInfo() {
    byte[] configBytes = serverIdentity.getAdditionalInfo();

    try {
      ConfigurationInfo configInfo = ConfigurationInfo.parseFrom(configBytes);
      // TODO(#2347): Check that ConfigurationInfo does not have additional/unknown fields.
      if (!configurationVerifier.test(configInfo)) {
        logger.log(Level.WARNING, "Verification of ConfigurationInfo failed.");
        return false;
      }
      // TODO(#2316): Verify proof of inclusion in Rekor
    } catch (InvalidProtocolBufferException e) {
      logger.log(Level.WARNING, "Could not create ConfigurationInfo from byte array:", e);
      return false;
    }
    return true;
  }

  /**
   * Verifies the attestation info, by reconstructing `attestationReport` from the hashes of the
   * signing public key and the configuration info. Returns false if this hash is different from the
   * `attestationReport` retrieved from the deserialized {@code ServerIdentity}.
   * @return
   */
  boolean verifyAttestationInfo() {
    byte[] configBytes = serverIdentity.getAdditionalInfo();

    try {
      AttestationInfo attestationInfo =
          AttestationInfo.parseFrom(serverIdentity.getAttestationInfo());
      byte[] attestationReport = attestationInfo.getReport().getData().toByteArray();

      byte[] publicKeyHash =
          Hashing.sha256().hashBytes(serverIdentity.getSigningPublicKey()).asBytes();
      byte[] configHash = Hashing.sha256().hashBytes(configBytes).asBytes();
      byte[] buffer = ByteBuffer.allocate(publicKeyHash.length + configHash.length)
                          .put(publicKeyHash)
                          .put(configHash)
                          .array();
      byte[] hashBytes = Hashing.sha256().hashBytes(buffer).asBytes();

      // Verify attestationReport
      if (!Arrays.equals(hashBytes, attestationReport)) {
        logger.log(Level.WARNING, "Invalid hash of the configuration data");
        return false;
      }

      // TODO(#1867): Add remote attestation support.
    } catch (InvalidProtocolBufferException e) {
      logger.log(Level.WARNING, "Could not parse bytes into ConfigurationInfo:", e);
      return false;
    }
    return true;
  }
}
