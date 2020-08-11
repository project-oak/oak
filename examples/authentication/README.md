# OpenID Connect Authentication Example

This example authenticates using the
[Google Identity Platform](https://developers.google.com/identity/), which
implements OpenID Connect.

The client application opens a browser which allows the user to authenticate. On
successful authentication, the browser is redirected to a web server running on
localhost. The authentication code is extracted from the query string of the
redirection URL and returned to the main thread.

The authorisation code can then be exchanged for an identity token by the
authentication service running as part of the Oak Runtime. The client calls the
authentication service via gRPC to make this exchange.

The Oak server requires a valid OAuth Client ID to enable the authentication
service. The client ID can be created as described in
https://developers.google.com/identity/protocols/oauth2/openid-connect#getcredentials

The Oak server can be run with the OpenID Connect authentication service enabled
using the --oidc-client flag:

```bash
cargo run --manifest-path=oak/server/rust/oak_loader/Cargo.toml -- \
    --application=<APP_CONFIG_PATH> \
    --grpc-tls-private-key=<PRIVATE_KEY_PATH> \
    --grpc-tls-certificate=<CERTIFICATE_PATH> \
    --root-tls-certificate=<CERTIFICATE_PATH> \
    --oidc-client=<OIDC_CLIENT_ID_PATH>
```

An example OpenID Connect Client Identity file can be downloaded from (only
accessible to authorized users):
https://pantheon.corp.google.com/apis/credentials/oauthclient/691249393555-0h52jim9ni9clkpd5chi82q9ccn44ebm.apps.googleusercontent.com?project=oak-ci

Click on `DOWNLOAD JSON` and save the file. This file contains sensitive
information, so **do not share this file or add it to the repository**.

To test the authentication client application with the downloaded file, run the
server using:

```bash
./scripts/runner run-examples \
    --example-name=hello_world \
    --client-variant=none \
    --server-additional-args=--oidc-client=./client_secret_691249393555-0h52jim9ni9clkpd5chi82q9ccn44ebm.apps.googleusercontent.com.json
```

While the Oak server is running with the OpenID Connect authentication service
enabled, the client can be executed using:

```bash
cargo run --manifest-path=examples/authentication/client/Cargo.toml
```

The client will log the returned identity token as an informational log message.
