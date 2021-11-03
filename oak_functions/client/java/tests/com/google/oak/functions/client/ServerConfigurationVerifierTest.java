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
import oak.functions.abi.ConfigurationInfo;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class ServerConfigurationVerifierTest {
  @Test
  public void testVerifyConfigurationInfo() {
    ConfigurationInfo configInfo = ConfigurationInfo.newBuilder().setMlInference(true).build();
    byte[] configBytes = configInfo.toByteArray();
    ServerIdentity serverIdentity =
        new ServerIdentity(new byte[] {}, new byte[] {}, new byte[] {}, new byte[] {}, configBytes);

    ServerConfigurationVerifier verifierExpectingMlInference = new ServerConfigurationVerifier(
        serverIdentity, (configInfoToVerify) -> configInfoToVerify.getMlInference());
    Assert.assertTrue(verifierExpectingMlInference.verify());

    ServerConfigurationVerifier verifierExpectingNoMlInference = new ServerConfigurationVerifier(
        serverIdentity, (configInfoToVerify) -> !configInfoToVerify.getMlInference());
    Assert.assertFalse(verifierExpectingNoMlInference.verify());
  }
}
