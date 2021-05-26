package com.google.oak.examples.grpc_attestation.client;

import com.google.oak.functions.client.AttestationClient;
import java.nio.charset.StandardCharsets;
import java.util.logging.Level;
import java.util.logging.Logger;

public class Main {
    private static Logger logger = Logger.getLogger(Main.class.getName());

    public static void main(String[] args) throws Exception {
        AttestationClient client = new AttestationClient("localhost:8080");

        byte[] request = "Example message".getBytes();
        byte[] response = client.Send(request);

        String decodedResponse = new String(response, StandardCharsets.UTF_8);
        logger.log(Level.INFO, "Client received response: " + decodedResponse);
    }
}
