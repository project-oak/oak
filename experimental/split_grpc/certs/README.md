# Certificates for local testing

These sample certificates are intended to be used for testing TLS on the local
loopback address only.

To create new versions of these certificates follow these steps:

Create a new secret key for the test CA certificate.

```bash
openssl genrsa -out ca.key 2048
```

Create a test CA certificate from the key.

```bash
openssl req -x509 -new -nodes -key ca.key -sha256 -days 3650 -out ca.pem
```

Create a new secret key for the TLS certificate.

```bash
openssl genrsa -out local.key 2048
```

Create a certificate signing request for the secret key.

```bash
openssl req -new -key local.key -out local.csr
```

Sign the TLS certificate using the test CA certificate, adding the extended
information in local.ext.

```bash
openssl x509 -req -in local.csr -CA ca.pem -CAkey ca.key -CAcreateserial \
  -out local.pem -days 3650 -sha256 -extfile local.ext
```

The local TLS certificate can be verified by running:

```bash
openssl verify -CAfile ca.pem local.pem
```

The local TLS certificate can be viewed by running:

```bash
openssl x509 -in local.pem -text -noout
```
