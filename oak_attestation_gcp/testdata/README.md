# Test Data for GCP Attestation

This directory contains test data, primarily JSON Web Tokens (JWTs), used for
testing GCP attestation verification logic.

## Overview

The tests require various JWTs to cover different scenarios:

* Valid tokens that should pass verification.
* Invalid tokens that should fail verification for specific reasons (e.g., bad
    signature, expired, invalid claims).

While some of these tokens may have been originally obtained from a live GCP
environment, it is not necessary to do so for adding new tests or updating
existing ones. For most cases, you can generate self-signed JWTs. The key is
that the token is structurally correct and signed by a key that corresponds
to the first certificate in the `x5c` header.

## Generating New Test JWTs

Here are the steps to generate a new self-signed JWT for testing purposes. This
process uses `openssl` for key and certificate generation and a tool like
[jwt.io](https://jwt.io) for assembling the JWT.

### 1. Generate an RSA Key Pair

First, create an RSA private and public key pair. These will be used to sign the
JWT and allow verifiers to check the signature.

```bash
# Generate a 2048-bit RSA private key
openssl genpkey -algorithm RSA -out private_key.pem -pkeyopt rsa_keygen_bits:2048

# Extract the public key from the private key
openssl rsa -pubout -in private_key.pem -out public_key.pem
```

### 2. Create a Self-Signed X.509 Certificate

The public key needs to be embedded in an X.509 certificate, which will then be
included in the JWT's `x5c` header.

```bash
# Create a self-signed certificate valid for 365 days
openssl req -new -x509 -key private_key.pem -out certificate.pem -days 365
```

You will be prompted to enter information for the certificate's subject. For
testing purposes, you can use dummy values.

### 3. Prepare the Certificate for the `x5c` Header

The `x5c` header in a JWT expects a JSON array of Base64-encoded certificate
strings. The PEM-encoded certificate from the previous step needs to be
converted.

First, strip the `-----BEGIN CERTIFICATE-----` and `-----END CERTIFICATE-----`
markers and remove all newlines.

```bash
# This command extracts the Base64 content of the certificate
cat certificate.pem | grep -v -- '---' | tr -d '\n'
```

Copy the output of this command. This is the string you will use in the JWT
header.

### 4. Assemble the JWT

Go to [jwt.io](https://jwt.io) to construct the token, make sure to select
"JWT Encoder".

1. **Header**: Update the header to include the `x5c` parameter, and use
    the RS256 algorithm.

    ```json
    {
      "alg": "RS256",
      "typ": "JWT",
      "x5c": ["<paste the Base64-encoded certificate from step 3 here>"]
    }
    ```

2. **Payload**: Define the claims for your test case.

3. **Signature**: In the "JWT Private Key" section, paste the content of
    `private_key.pem`.

The encoded JWT will be generated on the right. You can copy this and save it to
a new file in this directory to use in your tests.

## Creating Invalid Tokens for Testing

To test failure scenarios, you can create invalid tokens by modifying the process
above:

* **Bad Signature**: Sign the JWT with a different private key than the one
    corresponding to the certificate in the `x5c` header, or simply alter the
    signature bytes of a valid token.
* **Expired Token**: Set the `exp` claim in the payload to a timestamp in the
    past.
* **Invalid Issuer**: Change the `iss` claim to a value that the verifier will
    not accept.
* **Malformed Certificate**: Intentionally corrupt the Base64 certificate
    string in the `x5c` header.
