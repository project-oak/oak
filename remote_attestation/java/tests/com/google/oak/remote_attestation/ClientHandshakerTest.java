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

package com.google.oak.remote_attestation;

import com.google.oak.remote_attestation.ClientHandshaker;
import java.io.IOException;
import java.security.GeneralSecurityException;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

public class ClientHandshakerTest {
  private static final byte INVALID_MESSAGE_HEADER = 5;

  private ClientHandshaker handshaker;

  @Before
  public void setUp() {
    handshaker = new ClientHandshaker(new byte[0]);
  }

  @Test
  public void testCreateClientHello() throws GeneralSecurityException, IOException {
    Assert.assertEquals(handshaker.getState(), ClientHandshaker.State.Initializing);
    handshaker.createClientHello();
    Assert.assertEquals(handshaker.getState(), ClientHandshaker.State.ExpectingServerIdentity);
  }

  @Test(expected = IllegalStateException.class)
  public void testProcessServerIdentity() throws GeneralSecurityException, IOException {
    try {
      handshaker.processServerIdentity(new byte[0]);
    } catch (Exception e) {
      Assert.assertEquals(handshaker.getState(), ClientHandshaker.State.Aborted);
      throw e;
    }
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidMessage() throws GeneralSecurityException, IOException {
    try {
      handshaker.createClientHello();
      byte[] invalidMessage = {INVALID_MESSAGE_HEADER};
      handshaker.processServerIdentity(invalidMessage);
    } catch (Exception e) {
      Assert.assertEquals(handshaker.getState(), ClientHandshaker.State.Aborted);
      throw e;
    }
  }
}
