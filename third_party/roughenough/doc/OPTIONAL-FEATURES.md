# Optional Features

These features are **disabled by default** and must be explicitly enabled as 
described below.

* [HTTP Health Check responder](#http-health-check)
* [Key Management System (KMS) support](#key-management-system-kms-support)

# HTTP Health Check

## Description 

Intended for use by load balancers or other control plane facilities to monitor 
the state of Roughenough servers and remove unhealthy instances automatically. 

The server unconditionally emits a response to *any TCP connection* to the health
check port, then closes the connection:

```http
HTTP/1.1 200 OK
Content-Length: 0
Connection: Close

```

No attempt is made to parse the request, the server *always* emits this response. 

## How to enable

Provide a value for the `health_check_port` setting. This enables the HTTP 
health check responder on the configured port. 

```yaml
interface: 127.0.0.1
port: 8686
seed: f61075c988feb9cb700a4a6a3291bfbc9cab11b9c9eca8c802468eb38a43d7d3
health_check_port: 8000
```

## DoS Warning

**An unprotected health-check port can be used to DoS the server. Do NOT expose 
the health check port to the internet!** 

To accurately reflect the ability of a Roughenough server to respond to requests, 
the health check socket is serviced in the same event loop executing the primary Roughtime 
protocol. Abuse of the health-check port can denial-of-service the whole server.

If enabled, ensure the health check port is accessible only to the *intended load-balancer(s)
and/or control plane components*.


# Key Management System (KMS) Support

## Description 

The server's long-term identity can be protected by encrypting it, storing the encrypted value
in the configuration, and invoking a cloud key management system to temporarily decrypt 
(in memory) the long-term identity at server start-up. 

This way the server's long-term identity is never stored in plaintext. Instead the encrypted 
long-term identity "blob" is safe to store on disk, on Github, in a container, etc. Ability 
to access the unencrypted identity is controlled "out of band" by the KMS system.

## How to enable KMS support

KMS support must be compiled-in. To enable:

```bash
# Build with Google Cloud KMS support
$ cargo build --release --features "gcpkms"

# Build with AWS KMS support
$ cargo build --release --features "awskms"
```

## Google or Amazon: choose one and one only

Sadly, due to incompatibilities with dependencies of the KMS libraries, only **one** 
KMS system can be enabled at a time. Attempting `--features "awskms,gcpkms"` will result
in a build failure.

## Using `roughtime-kms` to encrypt the long-term seed

Use the command line tool `roughtime-kms` to encrypt the seed value for the 
server's long-term identity. To do this you will need: 

 1. The long-term key seed value 
 2. Access credentials for your cloud of choice
 3. An identifier for the KMS key to be used
 4. Necessary permissions to perform symmetric encrypt/decrypt operations
    using the selected key

For Amazon the key identifier is an ARN in the form:
```
arn:aws:kms:SOME_AWS_REGION:111122223333:key/1234abcd-12ab-34cd-56ef-1234567890ab
```

For Google the key identifier is a resource ID in the form:
```
projects/PROJECT_NAME/locations/GCP_LOCATION/keyRings/KEYRING_NAME/cryptoKeys/KEY_NAME
```

### AWS Example

#### Credentials 

[Rusoto](https://rusoto.org/) is used by Roughenough to access AWS. If your system
has AWS credentials in the typical `~/.aws/credentials` then everything should "just work".

Otherwise Rusoto supports alternative ways to provide AWS credentials. See 
[Rusoto's documentation](https://github.com/rusoto/rusoto/blob/master/AWS-CREDENTIALS.md) 
for details.

#### `roughenough-kms` Command line

```bash
# Provide AWS credentials as described in the Rusoto docs

# Build roughenough with AWS KMS support
$ cargo build --release --features "awskms"

# Encrypt the seed value
$ target/release/roughenough-kms \
  -k arn:aws:kms:SOME_AWS_REGION:111122223333:key/1234abcd-12ab-34cd-56ef-1234567890ab \
  -s a0a31d76900080c3cdc42fe69de8dd0086d6b54de7814004befd0b9c4447757e
  
# Output of above will be something like this
kms_protection: "arn:aws:kms:SOME_AWS_REGION:111122223333:key/1234abcd-12ab-34cd-56ef-1234567890ab"
seed: b8000c000102020078d39e85c7386e9e2bed1f30fac6dd322db96b8aaac8974fc6c0e0f566f8f6c971012fca1e69fffffd947fe82a9e505baf580000007e307c06092a864886f70d010706a06f306d020100306806092a864886f70d010701301e060960864801650304012e3011040c55d16d891b3b2a1ae2587a9c020110803bcc74dd96336009087772b28ec908c40e4113b1ab9b98934bd3b4f3dd3c1e8cdc6da82a4321fd8378ad0e2e0507bf0c5ea0e28d447e5f8482533baa423b7af8459ae87736f381d87fe38c21a805fae1c25c43d59200f42cae0d07f741e787a04c0ad72774942dddf818be0767e4963fe5a810f734a0125c
```

#### Configuration

Copy and paste the output `kms_protection` and `seed` values into a config or
set the corresponding environment variables. The `roughenough-server` will detect that
AWS KMS is being used and decrypt the seed automatically. For example:

```yaml
interface: 127.0.0.1
port: 8686
kms_protection: "arn:aws:kms:SOME_AWS_REGION:111122223333:key/1234abcd-12ab-34cd-56ef-1234567890ab"
seed: b8000c000102020078d39e85c7386e9e2bed1f30fac6dd322db96b8aaac8974fc6c0e0f566f8f6c971012fca1e69fffffd947fe82a9e505baf580000007e307c06092a864886f70d010706a06f306d020100306806092a864886f70d010701301e060960864801650304012e3011040c55d16d891b3b2a1ae2587a9c020110803bcc74dd96336009087772b28ec908c40e4113b1ab9b98934bd3b4f3dd3c1e8cdc6da82a4321fd8378ad0e2e0507bf0c5ea0e28d447e5f8482533baa423b7af8459ae87736f381d87fe38c21a805fae1c25c43d59200f42cae0d07f741e787a04c0ad72774942dddf818be0767e4963fe5a810f734a0125c
```

or using environment based configuration:

```bash
$ export ROUGHENOUGH_INTERFACE=127.0.0.1
$ export ROUGHENOUGH_PORT=8686
$ export ROUGHENOUGH_KMS_PROTECTION="arn:aws:kms:SOME_AWS_REGION:111122223333:key/1234abcd-12ab-34cd-56ef-1234567890ab"
$ export ROUGHENOUGH_SEED=b8000c000102020078d39e85c7386e9e2bed1f30fac6dd322db96b8aaac8974fc6c0e0f566f8f6c971012fca1e69fffffd947fe82a9e505baf580000007e307c06092a864886f70d010706a06f306d020100306806092a864886f70d010701301e060960864801650304012e3011040c55d16d891b3b2a1ae2587a9c020110803bcc74dd96336009087772b28ec908c40e4113b1ab9b98934bd3b4f3dd3c1e8cdc6da82a4321fd8378ad0e2e0507bf0c5ea0e28d447e5f8482533baa423b7af8459ae87736f381d87fe38c21a805fae1c25c43d59200f42cae0d07f741e787a04c0ad72774942dddf818be0767e4963fe5a810f734a0125c
```

### GCP Example

#### Credentials

Only **Service Account credentials** (in `.json` format) are currently supported. OAuth, bearer tokens, 
GAE default credentials, and GCE default credentials are **not** supported (contributions to
add support are particularly welcome!).

To obtain Service Account credentials if you don't already have them:

* Creating a new service account?
    1. Create the account 
    2. Download the credentials when prompted
    
* Existing service account?
    1. Open the Cloud Console (https://console.cloud.google.com)
    2. Navigate to `IAM -> Service accounts`
    3. Locate the service account row, click on its "Actions" menu (the three dots on the right) 
    4. Choose `Create key` and `JSON` format
    5. Download the credentials when prompted

Make note of the full path where the credentials are saved, it's needed in the next step.

#### `roughenough-kms` Command line

```bash
# Set environment variable pointing to downloaded Service Account credentials
$ export GOOGLE_APPLICATION_CREDENTIALS=/path/to/creds.json 

# Build roughenough with Google KMS support
$ cargo build --release --features "gcpkms"

# Encrypt the seed value
$ target/release/roughenough-kms \
  -k projects/PROJECT_NAME/locations/GCP_LOCATION/keyRings/KEYRING_NAME/cryptoKeys/KEY_NAME \
  -s a0a31d76900080c3cdc42fe69de8dd0086d6b54de7814004befd0b9c4447757e
  
# Output of above will be something like this
kms_protection: "projects/PROJECT_NAME/locations/GCP_LOCATION/keyRings/KEYRING_NAME/cryptoKeys/KEY_NAME"
seed: 71000c000a2400c7f2553954873ef29aeb37384c25d7a937d389221207c3368657870129d601d084c8da1249008d6fd4640f815596788e97bb3ce02fd007bc25a1019ca51945c3b99283d3945baacd77b1b991f5f6f8848c549a5767f57c9c999e97fe6d28fdb17db1d63c2ea966d8236d20c71e8e9c757c5bab62472c65b48376bc8951700aceb22545fce58d77e7cc147f7134da7a2cca790b54f29e4798442cee6e0d34e57f80ce983f7e5928cceff2
```

#### Configuration

Copy and paste the output `kms_protection` and `seed` values into a config or
set the corresponding environment variables. `roughenough-server` will detect that
Google KMS is being used and decrypt the seed automatically. For example:

```yaml
interface: 127.0.0.1
port: 8686
kms_protection: "projects/PROJECT_NAME/locations/GCP_LOCATION/keyRings/KEYRING_NAME/cryptoKeys/KEY_NAME"
seed: 71000c000a2400c7f2553954873ef29aeb37384c25d7a937d389221207c3368657870129d601d084c8da1249008d6fd4640f815596788e97bb3ce02fd007bc25a1019ca51945c3b99283d3945baacd77b1b991f5f6f8848c549a5767f57c9c999e97fe6d28fdb17db1d63c2ea966d8236d20c71e8e9c757c5bab62472c65b48376bc8951700aceb22545fce58d77e7cc147f7134da7a2cca790b54f29e4798442cee6e0d34e57f80ce983f7e5928cceff2
```

or using environment based configuration:

```bash
$ export ROUGHENOUGH_INTERFACE=127.0.0.1
$ export ROUGHENOUGH_PORT=8686
$ export ROUGHENOUGH_KMS_PROTECTION="projects/PROJECT_NAME/locations/GCP_LOCATION/keyRings/KEYRING_NAME/cryptoKeys/KEY_NAME"
$ export ROUGHENOUGH_SEED=71000c000a2400c7f2553954873ef29aeb37384c25d7a937d389221207c3368657870129d601d084c8da1249008d6fd4640f815596788e97bb3ce02fd007bc25a1019ca51945c3b99283d3945baacd77b1b991f5f6f8848c549a5767f57c9c999e97fe6d28fdb17db1d63c2ea966d8236d20c71e8e9c757c5bab62472c65b48376bc8951700aceb22545fce58d77e7cc147f7134da7a2cca790b54f29e4798442cee6e0d34e57f80ce983f7e5928cceff2
```
