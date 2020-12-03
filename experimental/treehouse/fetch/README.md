# Fetch

`fetch` is a tool that authenticates to Google APIs via Oauth2 and dumps data
for a single user.

# Setup

Navigate to the Google Cloud API Credentials page and download the client secret
in JSON format to the root of the repository (without renaming it):

**Make sure not to check in the client config**

https://pantheon.corp.google.com/apis/credentials/oauthclient/691249393555-anhtgr54cajv9l96apgfi3hv1n3a63e2.apps.googleusercontent.com?project=oak-ci

# Run

```
cargo run --manifest-path=experimental/treehouse/fetch/Cargo.toml
```

When prompted, click on the link that is printed to the terminal, and log in
with your @google.com account.

This only happens the first time, then the OAuth token is saved in a
`.oauth_token.secret` file and reused for future invocations.

**Make sure not to check in the OAuth token**
