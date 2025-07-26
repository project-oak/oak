"""Bazel macros for generating JWTs and ECDSA keys."""

def jwt_token(name, claims, signing_key, signing_cert, root_ca_cert):
    """Generates a JWT token from a claims file.

    Args:
        name: The name of the target.
        claims: The label of the claims JSON file.
        signing_key: The label of the signing key PEM file.
        signing_cert: The label of the signing cert PEM file.
        root_ca_cert: The label of the root CA cert PEM file.
    """
    native.genrule(
        name = name,
        srcs = [
            claims,
            signing_key,
            signing_cert,
            root_ca_cert,
            "//oak_attestation_gcp/jwtgen:jwtgen",
        ],
        outs = ["{}.jwt".format(name)],
        cmd = "cat $(location {}) | $(location //oak_attestation_gcp/jwtgen:jwtgen) --signing-key $(location {}) --signing-cert $(location {}) --root-ca-cert $(location {}) > $@".format(
            claims,
            signing_key,
            signing_cert,
            root_ca_cert,
        ),
    )

def ecdsa_p256_key_pair(name, visibility = None):
    """Generates a P-256 ECDSA key pair and exposes them in a filegroup.

    Args:
        name: The base name for the generated keys and the filegroup.
        visibility: The visibility of the filegroup.
    """
    private_key_file = name + ".key.pem"
    public_key_file = name + ".pub.pem"
    private_key_gen_rule = name + "_private_key"
    public_key_gen_rule = name + "_public_key"

    native.genrule(
        name = private_key_gen_rule,
        outs = [private_key_file],
        cmd = "openssl genpkey -algorithm EC -pkeyopt ec_paramgen_curve:P-256 -out $@",
    )

    native.genrule(
        name = public_key_gen_rule,
        srcs = [":" + private_key_gen_rule],
        outs = [public_key_file],
        cmd = "openssl pkey -in $< -pubout -out $@",
    )

    native.filegroup(
        name = name,
        srcs = [
            ":" + private_key_gen_rule,
            ":" + public_key_gen_rule,
        ],
        visibility = visibility,
    )

def rsa_key_pair(name, visibility = None):
    """Generates an RSA key pair and exposes them in a filegroup.

    Args:
        name: The base name for the generated keys and the filegroup.
        visibility: The visibility of the filegroup.
    """
    private_key_file = name + ".key.pem"
    public_key_file = name + ".pub.pem"
    private_key_gen_rule = name + "_private_key"
    public_key_gen_rule = name + "_public_key"

    native.genrule(
        name = private_key_gen_rule,
        outs = [private_key_file],
        cmd = "openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -out $@",
    )

    native.genrule(
        name = public_key_gen_rule,
        srcs = [":" + private_key_gen_rule],
        outs = [public_key_file],
        cmd = "openssl pkey -in $< -pubout -out $@",
    )

    native.filegroup(
        name = name,
        srcs = [
            ":" + private_key_gen_rule,
            ":" + public_key_gen_rule,
        ],
        visibility = visibility,
    )

def x509_cert(
        name,
        signing_key,
        subject,
        days,
        ca_cert = None,
        ca_key = None,
        faketime = None,
        visibility = None):
    """Generates an X.509 certificate.

    If `ca_cert` and `ca_key` are specified, the certificate will be signed
    by the given CA. Otherwise it will be self-signed.

    Args:
        name: The name of the target.
        signing_key: The private key to sign the certificate with.
        subject: The subject of the certificate.
        days: The number of days the certificate is valid for.
        ca_cert: The optional CA certificate.
        ca_key: The optional CA private key.
        faketime: If not None, the timestamp to use for certificate generation.
        visibility: The visibility of the generated certificate.
    """
    prefix = ""
    if faketime:
        prefix = "datefudge -s '{faketime}'".format(faketime = faketime)

    if ca_cert and ca_key:
        csr_target = "_" + name + "_csr"
        csr_file = name + ".csr"
        cert_file = name + ".pem"

        native.genrule(
            name = csr_target,
            srcs = [signing_key],
            outs = [csr_file],
            cmd = "{prefix} openssl req -new -key $(location {signing_key}) -out $@ -subj '{subject}'".format(
                prefix = prefix,
                signing_key = signing_key,
                subject = subject,
            ),
        )

        native.genrule(
            name = name,
            srcs = [
                ":" + csr_target,
                ca_cert,
                ca_key,
            ],
            outs = [cert_file],
            cmd = "{prefix} openssl x509 -req -in $(location :{csr_target}) -CA $(location {ca_cert}) -CAkey $(location {ca_key}) -CAcreateserial -out $@ -days {days} -sha256".format(
                prefix = prefix,
                csr_target = csr_target,
                ca_cert = ca_cert,
                ca_key = ca_key,
                days = days,
            ),
            visibility = visibility,
        )
    else:
        native.genrule(
            name = name,
            srcs = [signing_key],
            outs = ["{name}.pem".format(name = name)],
            cmd = "{prefix} openssl req -x509 -new -nodes -key $(location {signing_key}) -sha256 -days {days} -out $@ -subj '{subject}'".format(
                prefix = prefix,
                signing_key = signing_key,
                days = days,
                subject = subject,
            ),
            visibility = visibility,
        )

def sign_file(name, file_to_sign, signing_key, visibility = None):
    """Signs a file using a private key.

    Args:
        name: The name of the target.
        file_to_sign: The file to sign.
        signing_key: The private key to sign the file with.
        visibility: The visibility of the generated signature.
    """
    signature_file = name + ".sig"
    native.genrule(
        name = name,
        srcs = [
            signing_key,
            file_to_sign,
        ],
        outs = [signature_file],
        cmd = "openssl dgst -sha256 -sign $(location {signing_key}) -out $@ $(location {file_to_sign})".format(
            signing_key = signing_key,
            file_to_sign = file_to_sign,
        ),
        visibility = visibility,
    )
