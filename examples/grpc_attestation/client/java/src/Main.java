package com.google.oak.examples.grpc_attestation.client;

import com.google.oak.functions.client.AttestationClient;
import java.nio.charset.StandardCharsets;

public class Main {
    public static void main(String[] args) throws Exception {
        AttestationClient client = new AttestationClient("localhost:8080");

        byte[] request = "Example message".getBytes();
        byte[] response = client.Send(request);

        String decodedResponse = new String(response, StandardCharsets.UTF_8);
        System.out.printf("Client received response: %s\n", decodedResponse);
    }
}
