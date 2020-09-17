# Oak Chrome Extension

The Oak Chrome Extension is a proof of concept to show how Oak may be used as
part of web applications.

A regular web page may at any point enter Oak private mode, which means that
from that point onwards it will be able to communicate exclusively with an Oak
application that can enforce that any data it receives is kept private for the
current session. This is similar to "incognito mode" but for the server-side
parts of an application.

A web page enters Oak private mode by invoking the following Javascript code:

```javascript
window.postMessage('oak_enter');
```

This is an irreversible process: at this point, the Oak extension takes full
control of all the communication initiated by that particular tab, blocks any
non-Oak requests (including any static assets, which the application should take
care to load before entering Oak mode), attaches an appropriate label to any Oak
requests, and authenticates against a remote Oak application.

Note that there is no way of getting out of Oak mode for a tab; if there were,
it may be used to leak potentially confidential data from the current tab. The
only way out of Oak mode is to manually close the tab, and then create a new
one. Again, this is similar to how it is not possible to take a Chrome incognito
tab and turn it back into a regular tab.

Note: for now, it seems that closing a tab and then re-opening the last closed
tab actually re-creates a tab with the same URL but outside of Oak mode.

## Installation

In order to install the Chrome extension locally for development:

- navigate to `chrome://extensions`
- turn on "Developer mode"
- click on the "Load unpacked" button
- select the `chrome_extension` folder (the one containing the `manifest.json`
  file) and click "Open"

After the extension is installed, in order to reload it from disk, it is
sufficient to click on the refresh arrow button next to the extension.
