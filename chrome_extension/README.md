# Oak Chrome Extension

The Oak Chrome Extension is a proof of concept to show how Oak may be used as
part of web applications.

In its current state, the extension can load a given website into a secure
sandbox that prevents it from leaking information entered into it. For example
it can enforce that a website performing base64 encoding does so locally only.

This enforcement works by using two mechanisms in conjunction:

- It renders the source code of the website in an iframe, utilizing the
  `frame-src: 'unsafe-inline'`
  [Content-Security-Policy](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Content-Security-Policy)
  alongside the
  [sandbox attribute](https://developer.mozilla.org/en-US/docs/Web/HTML/Element/iframe#attr-sandbox)
  to prevent from leaking data through navigation.
- It applies the
  [Content-Security-Policy](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Content-Security-Policy)
  of `sandbox allow-scripts; default-src 'unsafe-inline';` to prevent network
  calls, and stop leaks via cookies/localStorage/postMessage/etc.

To load a website into this secure context, the user clicks the red extension
icon.

<img src="icon-red.png" alt="drawing" width="32" height="32"/>

When viewing a page in this secure context the extension icon turns green.

<img src="icon-green.png" alt="drawing" width="32" height="32"/>

Naturally, not all websites will work in this secure sandbox. Some might appear
broken. To comply with the security restrictions, all assets required for the
functionality of the page must be inlined into the document. It cannot load
external assets or rely on computations performed on a server.

An example of page that does this would be
[https://csp-locked-client-side-base64.web.app](https://csp-locked-client-side-base64.web.app),
which performs base64 encoding/decoding on-device.

In the future, once browsers implement the
[navigate-to](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Content-Security-Policy/navigate-to)
draft, all enforcement could be done using
[Content-Security-Policies](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Content-Security-Policy)
only.

Addtionally, this extension can be extended to permit communication with trusted
Oak servers.

## Installation

In order to install the Chrome extension locally for development:

- navigate to `chrome://extensions`
- turn on "Developer mode"
- click on the "Load unpacked" button
- select the `chrome_extension` folder (the one containing the `manifest.json`
  file) and click "Open"

After the extension is installed, in order to reload it from disk, it is
sufficient to click on the refresh arrow button next to the extension.
