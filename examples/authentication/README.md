# OpenID Connect Authentication Example

This example authenticates using the
[Google Identity Platform](https://developers.google.com/identity/), which
implements OpenID Connect.

The client application opens a browser which allows the user to authenticate. On
successful authentication, the browser is redirected to a web server running on
localhost. The authentication code is extracted from the query string of the
redirection URL and returned to the main thread.

The authorisation code can then be exchanged for an identity token by the
authentication server. The client calls the authentication server via gRPC to
make this exchange.

The server requires a valid OAuth Client ID, which can be created as described
in
https://developers.google.com/identity/protocols/oauth2/openid-connect#getcredentials

The server can be run using:

```bash
cargo run --package=auth_server -- \
  --client-id=<CLIENT_ID> \
  --client-secret=<CLIENT_SECRET>
```

Example values for `<CLIENT_ID>` and `<CLIENT_SECRET>` can be copied (only
accessible to authorized users) from
https://pantheon.corp.google.com/apis/credentials/oauthclient/691249393555-0h52jim9ni9clkpd5chi82q9ccn44ebm.apps.googleusercontent.com?project=oak-ci

While the server is running, the client can be executed using:

```bash
cargo run --package=auth_client
```

The client will log the returned identity token as an informational log message.
