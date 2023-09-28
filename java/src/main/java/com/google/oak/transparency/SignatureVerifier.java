//
// Copyright 2023 The Project Oak Authors
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

package com.google.oak.transparency;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Optional;

/** Verifies a signature based on a public key. */
public class SignatureVerifier {
    /**
     * Needs three paths as command line arguments, corresponding to the arguments
     * of {@code #verify()}. Verification failure is signalled via exit code.
     */
    public static void main(String[] args) throws Exception {
        if (args.length != 3) {
            System.exit(2);
        }

        String signature = Files.readString(Path.of(args[0]));
        byte[] publicKeyBytes = Files.readAllBytes(Path.of(args[1]));
        byte[] contentBytes = Files.readAllBytes(Path.of(args[2]));

        Optional<Failure> failure = verify(signature, publicKeyBytes, contentBytes);
        if (failure.isPresent()) {
            System.err.println("Verification failed: " + failure.get().getMessage());
            System.exit(1);
        }
    }

    private static Optional<Failure> failure(String message) {
        return Optional.of(new Failure(message));
    }

    /**
     * Verifies the signature over content bytes using a public key.
     *
     * @param signature      The base64-encoded signature
     * @param publicKeyBytes The PEM-encoded public key
     * @param contentBytes   The serialized content
     * @return Empty if the verification succeeds, or a failure otherwise
     */
    public static Optional<Failure> verify(
            String signature, byte[] publicKeyBytes, byte[] contentBytes) {
        if (signature == null || signature.length() == 0) {
            return failure("empty signature");
        }
        if (contentBytes == null || contentBytes.length == 0) {
            return failure("empty content");
        }
        if (publicKeyBytes == null || publicKeyBytes.length == 0) {
            return failure("empty public key");
        }
        // TODO(#2854): verify the signature
        return Optional.empty();
    }

    private SignatureVerifier() {
    }
}
