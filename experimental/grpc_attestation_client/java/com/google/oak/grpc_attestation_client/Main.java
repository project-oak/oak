package com.google.oak.grpc_attestation_client;

import com.google.oak.grpc_attestation_client.AttestationClient;
import java.util.logging.Level;
import java.util.logging.Logger;

public class Main {
// public class GrpcAttestationClient {
    private static final Logger logger = Logger.getLogger(Main.class.getName());
    // private static final Logger logger = Logger.getLogger(GrpcAttestationClient.class.getName());

    public static void main(String[] args) throws InterruptedException {
        AttestationClient client = new AttestationClient("localhost:8080");
        // String target = "localhost:8080";
        // ManagedChannel channel = ManagedChannelBuilder
        //     // .forAddress("localhost", 8080)
        //     .forTarget(target)
        //     .usePlaintext()
        //     .build();

        // // GrpcAttestationGrpc.GrpcAttestationBlockingStub stub =
        // //     GrpcAttestationGrpc.newBlockingStub(channel);
        // GrpcAttestationStub stub = GrpcAttestationGrpc.newStub(channel);
        // // GrpcAttestationGrpc.GrpcAttestationStub stub = GrpcAttestationGrpc.newStub(channel);
        
        // String publicKey = "";
        // ByteString publicKeyBytes = ByteString.copyFromUtf8(publicKey);

        // // GetAttestedDataRequest request = GetAttestedDataRequest.newBuilder()
        // //     .setRequestType(
        // //         AttestationRequest.newBuilder()
        // //             .setPublicKey(publicKeyBytes)
        // //             .build()
        // //     )
        // //     .build();

        // // StreamObserver<RouteSummary> responseObserver = new StreamObserver<RouteSummary>() {
        // // StreamObserver<RouteNote> requestObserver = asyncStub.routeChat(new StreamObserver<RouteNote>() {

        // final CountDownLatch finishLatch = new CountDownLatch(1);

        // StreamObserver<GetAttestedDataResponse> responseObserver = new StreamObserver<GetAttestedDataResponse>() {
        //     @Override
        //     public void onNext(GetAttestedDataResponse response) {
        //         logger.log(Level.INFO, "Client received response: {0}", response);
        //     }

        //     @Override
        //     public void onError(Throwable t) {
        //         Status status = Status.fromThrowable(t);
        //         logger.log(Level.WARNING, "Couldn't receive response: {0}", status);
        //     }

        //     @Override
        //     public void onCompleted() {
        //         logger.log(Level.INFO, "Server has finished the stream");
        //     }
        // };

        // StreamObserver<GetAttestedDataRequest> requestObserver = stub.getAttestedData(responseObserver);
        // try {
        //     GetAttestedDataRequest[] requests = {
        //         GetAttestedDataRequest.newBuilder()
        //             .setAttestationRequest(
        //                 AttestationRequest.newBuilder()
        //                     .setPublicKey(publicKeyBytes)
        //                     .build()
        //             )
        //             .build()
        //     };

        //     for (GetAttestedDataRequest request : requests) {
        //         logger.log(Level.INFO, "Client sends request: {0}", request);
        //         requestObserver.onNext(request);
        //     }
        // } catch (RuntimeException e) {
        //     // Cancel RPC
        //     logger.log(Level.WARNING, "Couldn't send request");
        //     // logger.log(Level.WARNING, "Couldn't send request: {0}", status);
        //     requestObserver.onError(e);
        //     throw e;
        // }
        // // Mark the end of requests
        // logger.log(Level.INFO, "Client has finished the stream");
        // requestObserver.onCompleted();

        // // GetAttestedDataResponse response = stub.getAttestedData(request);

        // // System.out.println(response);

        // // Receiving happens asynchronously
        // finishLatch.await(1, TimeUnit.MINUTES);

        // channel.shutdown();
    }
}
    