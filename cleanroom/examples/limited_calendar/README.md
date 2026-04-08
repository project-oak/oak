# Limited Calendar Example

This example demonstrates a Wasm module that accesses a user's Google Calendar
using an OAuth token, but enforces Information Flow Control (IFC) to ensure the
module can only return events within a specific time window (10 days before and
after a simulated current date).

## How it works

1. **Secrecy label**: The module is spawned with
   `--secrecy=caller,calendar_token`, which sets its initial secrecy to
   `{caller, calendar_token}`. This allows it to read cells labeled with
   `calendar_token`.
2. **Input**: The module reads the Calendar ID (usually the user's email) from
   `stdin`.
3. **Privilege**: The module uses its privilege
   (`speaks_for = ["calendar_token", "caller"]`) to declassify both the secret
   cell label and the caller's confidentiality before making a network request.
4. **Network I/O**: The module makes an HTTP request to Google Calendar API,
   using `timeMin` and `timeMax` parameters to filter events server-side.
5. **Filtering**: The module also checks the results in Wasm to ensure they
   match the criteria (defense in depth).

## How to run

### 1. Get an OAuth Token

You can generate a temporary OAuth token for testing using the Google OAuth
Playground:

1. Go to
   [Google OAuth Playground](https://developers.google.com/oauthplayground).
2. In Step 1 (Select & authorize APIs), scroll down to **Calendar API v3** and
   select `https://www.googleapis.com/auth/calendar.readonly`.
3. Click **Authorize APIs** and log in with your Google account.
4. In Step 2 (Exchange authorization code for tokens), click **Exchange
   authorization code for tokens**.
5. Copy the **Access Token** (starts with `ya29...`).

### 2. Configure Cells

Add the token to `cleanroom/example_cells.toml`:

```toml
[[cell]]
name      = "google_oauth_token"
value     = "ya29.your_actual_token_here"
secrecy   = ["calendar_token"]
integrity = ["caller"]
```

### 3. Run the Example

Ensure the server is running with the updated policy and cells.

Run the client, passing your email as input to stdin:

```bash
bazel run cleanroom -- shell
echo "your_email@gmail.com" | cleanroom run limited_calendar_wasm \
  --secrecy=caller,calendar_token
```

Note: The example hardcodes a simulated current date of `2014-04-09` to match
test data. If you are using a real calendar with current events, you may need to
update the simulated date in `wasm.rs` to see results.
