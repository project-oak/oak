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
import oak.functions.abi.ConfigurationInfo;

/**
 * A verifier that verifies the {@code ConfigurationInfo} in an instance of {@code ServerIdentity}
 * based on a given predicate.
 */
public class ServerConfigurationVerifier {
  private static final Logger logger =
      Logger.getLogger(ServerConfigurationVerifier.class.getName());
  private final ServerIdentity serverIdentity;
  private final Predicate<ConfigurationInfo> configurationVerifier;

  public ServerConfigurationVerifier(
      ServerIdentity serverIdentity, Predicate<ConfigurationInfo> configurationVerifier) {
    this.serverIdentity = serverIdentity;
    this.configurationVerifier = configurationVerifier;
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
  public boolean verify() {
    byte[] configBytes = serverIdentity.getAdditionalInfo();

    try {
      ConfigurationInfo configInfo =
          ConfigurationInfo.parseFrom(configBytes, ExtensionRegistryLite.getEmptyRegistry());
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
}
