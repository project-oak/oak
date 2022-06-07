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

import com.google.oak.remote_attestation.Message.ServerIdentity;
import com.google.protobuf.ExtensionRegistryLite;
import com.google.protobuf.InvalidProtocolBufferException;
import java.util.function.Predicate;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.functions.abi.ConfigurationReport;

/**
 * A verifier that verifies the {@code ConfigurationReport} in an instance of {@code ServerIdentity}
 * based on a given predicate.
 */
public class ServerConfigurationVerifier {
  private static final Logger logger =
      Logger.getLogger(ServerConfigurationVerifier.class.getName());
  private final ServerIdentity serverIdentity;
  private final Predicate<ConfigurationReport> configurationVerifier;

  public ServerConfigurationVerifier(
      ServerIdentity serverIdentity, Predicate<ConfigurationReport> configurationVerifier) {
    this.serverIdentity = serverIdentity;
    this.configurationVerifier = configurationVerifier;
  }

  /**
   * Verifies the {@code ConfigurationReport} in the {@code serverIdentity}.
   *
   * The `additionalInfo` field of {@code serverIdentity} is expected to contain an instance of
   * {@code ConfigurationReport} as a binary-encoded protobuf message. This byte array is parsed
   * into an instance of {@code ConfigurationReport}. Returns false if parsing fails. Otherwise
   * tests the {@code configurationVerifier} predicate for the resulting {@code
   * ConfigurationReport}, and returns the result.
   *
   * @return the result of calling test {@code configurationVerifier} as described above.
   */
  public boolean verify() {
    byte[] additionalAttestationData = serverIdentity.getAdditionalAttestationData();

    try {
      ConfigurationReport configInfo = ConfigurationReport.parseFrom(
          additionalAttestationData, ExtensionRegistryLite.getEmptyRegistry());
      // TODO(#2347): Check that ConfigurationReport does not have additional/unknown fields.
      if (!configurationVerifier.test(configInfo)) {
        logger.log(Level.WARNING, "Verification of ConfigurationReport failed.");
        return false;
      }
      // TODO(#2316): Verify proof of inclusion in Rekor
    } catch (InvalidProtocolBufferException e) {
      logger.log(Level.WARNING, "Could not create ConfigurationReport from byte array:", e);
      return false;
    }
    return true;
  }
}
