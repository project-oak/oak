# OpenID Connect Authentication Example

This example authenticates using the
[Google Identity Platform](https://developers.google.com/identity/), which
implements OpenID Connect.

The client application opens a browser which allows the user to authenticate. On
successful authentication, the browser is redirected to connect to a web server
running on localhost. The authentication code is extracted from the query string
of the redirection URL and returned to the main thread.

TODO(#855): The authenctication code can then be exchanged for an identity token
by the authentication server.

The client can be executed using:

```bash

cargo run -b auth_client -- --client-id $YOUR_CLIENT_ID

```

This requires a valid OAuth Client ID, which can be created as described in
https://developers.google.com/identity/protocols/oauth2/openid-connect#getcredentials
