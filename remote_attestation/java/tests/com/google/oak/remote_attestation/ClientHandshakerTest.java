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

import static org.junit.Assert.assertThrows;

import com.google.oak.remote_attestation.ClientHandshaker;
import java.io.IOException;
import java.security.GeneralSecurityException;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class ClientHandshakerTest {
  private static final byte INVALID_MESSAGE_HEADER = 5;

  private ClientHandshaker handshaker;

  @Before
  public void setUp() {
    handshaker = new ClientHandshaker(new byte[0]);
  }

  @Test
  public void testCreateClientHello() throws GeneralSecurityException, IOException {
    Assert.assertEquals(ClientHandshaker.State.INITIALIZING, handshaker.getState());
    handshaker.createClientHello();
    Assert.assertEquals(ClientHandshaker.State.EXPECTING_SERVER_IDENTITY, handshaker.getState());
  }

  @Test
  public void testProcessServerIdentity() throws GeneralSecurityException, IOException {
    assertThrows(IllegalStateException.class, () -> {
      try {
        handshaker.processServerIdentity(new byte[0]);
      } catch (Exception e) {
        Assert.assertEquals(ClientHandshaker.State.ABORTED, handshaker.getState());
        throw e;
      }
    });
  }

  @Test
  public void testInvalidMessage() throws GeneralSecurityException, IOException {
    assertThrows(IllegalArgumentException.class, () -> {
      try {
        handshaker.createClientHello();
        byte[] invalidMessage = {INVALID_MESSAGE_HEADER};
        handshaker.processServerIdentity(invalidMessage);
      } catch (Exception e) {
        Assert.assertEquals(ClientHandshaker.State.ABORTED, handshaker.getState());
        throw e;
      }
    });
  }
}
