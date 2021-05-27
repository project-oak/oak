package com.google.oak.functions.client;

import com.google.oak.functions.client.AeadEncryptor;
import com.google.oak.functions.client.KeyNegotiator;
import com.google.protobuf.ByteString;
import io.grpc.ManagedChannel;
import io.grpc.ManagedChannelBuilder;
import io.grpc.Status;
import io.grpc.stub.StreamObserver;
import java.lang.RuntimeException;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.functions.invocation.Request;
import oak.functions.invocation.Response;
import oak.functions.server.AttestedInvokeResponse;
import oak.functions.server.AttestedInvokeRequest;
import oak.functions.server.SecureRequest;
import oak.functions.server.ClientIdentity;
import oak.functions.server.ServerIdentity;
import oak.functions.server.RemoteAttestationGrpc;
import oak.functions.server.RemoteAttestationGrpc.RemoteAttestationStub;

// TODO(#2121): Implement a protocol independent state machine.
public class AttestationClient {
    private static Logger logger = Logger.getLogger(AttestationClient.class.getName());
    private ManagedChannel channel;
    private StreamObserver<AttestedInvokeRequest> requestObserver;
    private BlockingQueue<AttestedInvokeResponse> messageQueue;
    private AeadEncryptor encryptor;

    public AttestationClient(String uri) throws Exception {
        // Create gRPC channel.
        channel = ManagedChannelBuilder
            .forTarget(uri)
            .usePlaintext()
            .build();
        RemoteAttestationStub stub = RemoteAttestationGrpc.newStub(channel);

        // Create server response handler.
        messageQueue = new ArrayBlockingQueue<AttestedInvokeResponse>(1);
        StreamObserver<AttestedInvokeResponse> responseObserver = new StreamObserver<AttestedInvokeResponse>() {
            @Override
            public void onNext(AttestedInvokeResponse response) {
                try {
                    messageQueue.put(response);
                } catch (Exception e) {
                    logger.log(Level.WARNING, "Couldn't send server response to the message queue: " + e);
                }
            }

            @Override
            public void onError(Throwable t) {
                Status status = Status.fromThrowable(t);
                logger.log(Level.WARNING, "Couldn't receive response: " + status);
            }

            @Override
            public void onCompleted() {}
        };
        requestObserver = stub.attestedInvoke(responseObserver);

        // Generate client private/public key pair.
        KeyNegotiator keyNegotiator = new KeyNegotiator();
        byte[] publicKey = keyNegotiator.getPublicKey();
        ByteString publicKeyBytes = ByteString.copyFrom(publicKey);

        // Send client public key to the server.
        AttestedInvokeRequest request = AttestedInvokeRequest
            .newBuilder()
            .setClientIdentity(
                ClientIdentity.newBuilder()
                    .setPublicKey(publicKeyBytes)
                    .build()
            )
            .build();
        requestObserver.onNext(request);
        AttestedInvokeResponse response = (AttestedInvokeResponse) messageQueue.take();

        // Verify remote attestation.
        byte[] attestationInfo = response.getServerIdentity().getAttestationInfo().toByteArray();
        if (!verifyAttestation(attestationInfo)) {
            throw new RuntimeException("Couldn't verify attestation info");
        }

        // Generate session key and initialize AEAD encryptor based on it.
        byte[] peerPublicKey = response.getServerIdentity().getPublicKey().toByteArray();
        encryptor = keyNegotiator.createAeadEncryptor(peerPublicKey);
    }

    private Boolean verifyAttestation(byte[] attestationInfo) {
        // TODO(#1867): Add remote attestation support.
        return true;
    }

    protected void finalize() throws Throwable {
        requestObserver.onCompleted();
        channel.shutdown();
    }

    /**
     * Encrypts and sends `message` via an attested gRPC channel to the server.
     */
    public Response Send(Request request) throws Exception {
        byte[] encryptedMessage = encryptor.encrypt(request.toByteArray());
        SecureRequest secureRequest = SecureRequest.newBuilder()
                    .setEncryptedPayload(ByteString.copyFrom(encryptedMessage))
                    .build();
        AttestedInvokeRequest attestedRequest = AttestedInvokeRequest
            .newBuilder()
            .setRequest(secureRequest)
            .build();

        requestObserver.onNext(attestedRequest);
        AttestedInvokeResponse attestedResponse = (AttestedInvokeResponse) messageQueue.take();

        byte[] responsePayload = attestedResponse.getEncryptedPayload().toByteArray();
        byte[] decryptedResponse = encryptor.decrypt(responsePayload);
        Response response = Response.parseFrom(decryptedResponse);
        return response;
    }
}
