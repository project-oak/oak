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

package com.google.oak.session;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import com.google.oak.session.OakSessionConfigBuilder.AttestationType;
import com.google.oak.session.OakSessionConfigBuilder.HandshakeType;
import com.google.oak.session.v1.PlaintextMessage;
import com.google.oak.session.v1.SessionRequest;
import com.google.oak.session.v1.SessionResponse;
import com.google.protobuf.ByteString;
import java.nio.charset.Charset;
import java.util.Arrays;
import java.util.Optional;
import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class OakSessionTest {
  private OakClientSession clientSession;
  private OakServerSession serverSession;

  @BeforeClass
  public static void setUpClass() {
    OakClientSession.loadNativeLib();
    OakServerSession.loadNativeLib();
  }

  @Before
  public void setUp() {
    clientSession = new OakClientSession(
        new OakSessionConfigBuilder(AttestationType.UNATTESTED, HandshakeType.NOISE_NN));
    serverSession = new OakServerSession(
        new OakSessionConfigBuilder(AttestationType.UNATTESTED, HandshakeType.NOISE_NN));
  }

  @After
  public void tearDown() {
    serverSession.close();
    clientSession.close();
  }

  @Test
  public void testHandshakeUnattestedNN() throws Exception {
    doHandshake();
    assertTrue(clientSession.isOpen());
    assertTrue(serverSession.isOpen());
  }

  @Test
  public void testGetSessionBindingToken_matchingInfo_succeeds() throws Exception {
    doHandshake();
    byte[] clientSessionBindingToken = clientSession.getSessionBindingToken("info".getBytes());
    byte[] serverSessionBindingToken = serverSession.getSessionBindingToken("info".getBytes());
    assertTrue(clientSessionBindingToken.length > 0);
    assertTrue(serverSessionBindingToken.length > 0);
    assertArrayEquals(clientSessionBindingToken, serverSessionBindingToken);
  }

  @Test
  public void testGetSessionBindingToken_misMatchingInfo_fails() throws Exception {
    doHandshake();
    byte[] clientSessionBindingToken = clientSession.getSessionBindingToken("info".getBytes());
    byte[] serverSessionBindingToken =
        serverSession.getSessionBindingToken("wrong info".getBytes());
    assertTrue(clientSessionBindingToken.length > 0);
    assertTrue(serverSessionBindingToken.length > 0);
    assertFalse(Arrays.equals(clientSessionBindingToken, serverSessionBindingToken));
  }

  @Test
  public void testSendMessageClientToServer() {
    doHandshake();
    sendClientToServer("plaintext message");
  }

  @Test
  public void testSendMessageServerToClient() {
    doHandshake();
    sendServerToClient("plaintext message");
  }

  @Test
  public void testMessageSequence() {
    doHandshake();
    sendClientToServer("request 1");
    sendClientToServer("request 2");
    sendServerToClient("response 1");
    sendServerToClient("response 2");
    sendClientToServer("request 3");
  }

  @Test
  public void testWriteUnopenedClientSessionFails() throws Exception {
    assertThrows("session is not open", OakSessionException.class,
        () -> clientSession.write(PlaintextMessage.getDefaultInstance()));
  }

  @Test
  public void testWriteUnopenedServerSessionFails() throws Exception {
    assertThrows("session is not open", OakSessionException.class,
        () -> serverSession.write(PlaintextMessage.getDefaultInstance()));
  }

  @Test
  public void testUnexpectedRead() throws Exception {
    doHandshake();
    assertFalse(clientSession.read().isPresent());
    assertFalse(serverSession.read().isPresent());
  }

  @Test
  public void testUnexpectedGetOutgoingMessage() throws Exception {
    doHandshake();
    assertFalse(clientSession.getOutgoingMessage().isPresent());
    assertFalse(serverSession.getOutgoingMessage().isPresent());
  }

  private void doHandshake() {
    while (!clientSession.isOpen() || !serverSession.isOpen()) {
      Optional<SessionRequest> request = clientSession.getOutgoingMessage();
      assertTrue(request.isPresent());
      assertTrue(serverSession.putIncomingMessage(request.get()));
      Optional<SessionResponse> response = serverSession.getOutgoingMessage();
      assertTrue(response.isPresent());
      assertTrue(clientSession.putIncomingMessage(response.get()));
    }
  }

  private void sendClientToServer(String message) {
    PlaintextMessage plaintext =
        PlaintextMessage.newBuilder()
            .setPlaintext(ByteString.copyFrom(message, Charset.defaultCharset()))
            .build();
    clientSession.write(plaintext);
    Optional<SessionRequest> clientRequest = clientSession.getOutgoingMessage();
    assertTrue(clientRequest.isPresent());
    assertTrue(serverSession.putIncomingMessage(clientRequest.get()));
    assertEquals(plaintext, serverSession.read().get());
  }

  private void sendServerToClient(String message) {
    PlaintextMessage plaintext =
        PlaintextMessage.newBuilder()
            .setPlaintext(ByteString.copyFrom(message, Charset.defaultCharset()))
            .build();
    serverSession.write(plaintext);
    Optional<SessionResponse> serverRequest = serverSession.getOutgoingMessage();
    assertTrue(serverRequest.isPresent());
    assertTrue(clientSession.putIncomingMessage(serverRequest.get()));
    assertEquals(plaintext, clientSession.read().get());
  }
}
