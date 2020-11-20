# Oak Chrome Extension

The Oak Chrome Extension is a proof of concept to show how Oak may be used as
part of web applications.

At its current state, the extension detects a website can leak information
entered into it to outside servers. For example it can ensure that a website
performing base64 encoding does so locally only, and does not leak the entered
information.

This enforcement happens via the
[Content-Security-Policy](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Content-Security-Policy)
of
`sandbox allow-scripts; default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'`.
It prevents network calls, initiating navigation other pages.

Depending on whether a given website complies with this CSP or not, the
extension will show either a red or green icon.

<img src="icon-red.png" alt="drawing" width="32" height="32"/>

An example of page that does not impose this CSP and will show a red icon would
be [https://www.base64encode.org](https://www.base64encode.org/). In fact, it
sends the data that is entered to an external server.

<img src="icon-green.png" alt="drawing" width="32" height="32"/>

An example of page that does impose this CSP, is considered safe, and therefore
will show a green icon would be
[https://csp-locked-client-side-base64.web.app](https://csp-locked-client-side-base64.web.app).
It performs all operations on the device of the user.

In the future, this extension can be extended to allow users to apply this CSP
to any website (potentially breaking it in the process), or permit communication
with trusted Oak servers.

## Installation

In order to install the Chrome extension locally for development:

- navigate to `chrome://extensions`
- turn on "Developer mode"
- click on the "Load unpacked" button
- select the `chrome_extension` folder (the one containing the `manifest.json`
  file) and click "Open"

After the extension is installed, in order to reload it from disk, it is
sufficient to click on the refresh arrow button next to the extension.
