# OpenID Connect Authentication Example

This example authenticates using the
[Google Identity Platform](https://developers.google.com/identity/), which
implements OpenID Connect.

The client application opens a browser which allows the user to authenticate. On
successful authentication, the browser is redirected to connect to a web server
running on localhost. The authentication code is extracted from the query string
of the redirection URL and returned to the main thread.

TODO(#855): The authentication code can then be exchanged for an identity token
by the authentication server.

The client can be executed using:

```bash
cargo run --package=auth_client -- --client-id=691249393555-0h52jim9ni9clkpd5chi82q9ccn44ebm.apps.googleusercontent.com
```

This requires a valid OAuth Client ID, which can be created as described in
https://developers.google.com/identity/protocols/oauth2/openid-connect#getcredentials

The Client ID (and corresponding Client Secret) from the example script above
can be managed here (only accessible to authorized users):
https://pantheon.corp.google.com/apis/credentials/oauthclient/691249393555-0h52jim9ni9clkpd5chi82q9ccn44ebm.apps.googleusercontent.com?project=oak-ci
