/*
 * Copyright 2019 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

'use strict';

const GREEN_ICON_PATH = './icon-green.png';
const RED_ICON_PATH = './icon-red.png';

// Map of tabs that are applying the desired CSP. The key is the `tabId`, the
// value is the specific `url` that applies them. Keeping track of the URL is
// necessary since administrators can block access to the `chrome.webRequest`
// API used to check CSP on a per page basis. Without checking that the URL
// matches, a user could navigate from a secure page to a potentially
// insecure page whose CSP cannot be checked, and the tab would still be
// considered secure.
const tabsUsingDesiredCsp = new Map();

function setIconForTab(tabId, url) {
  const isUsingDesiredCsp =
    tabsUsingDesiredCsp.has(tabId) && tabsUsingDesiredCsp.get(tabId) === url;

  chrome.browserAction.setIcon({
    path: isUsingDesiredCsp ? GREEN_ICON_PATH : RED_ICON_PATH,
    tabId,
  });
}

chrome.tabs.onUpdated.addListener((tabId, changeInfo, tab) => {
  setIconForTab(tabId, tab.url);
});
chrome.tabs.onRemoved.addListener(tabsUsingDesiredCsp.delete);

function requestProcessor({ responseHeaders, tabId, url }) {
  const cspHeader = responseHeaders.find(
    (header) => header.name.toLowerCase() === 'content-security-policy'
  );

  // TODO(#1492): Parse the CSP to check whether it is as strict or stricter
  // than the minimum CSP, instead of just checking if the string matches.
  const isUsingDesiredCsp =
    cspHeader !== undefined &&
    cspHeader.value ===
      "default-src 'none'; sandbox allow-scripts; script-src 'unsafe-inline'; style-src 'unsafe-inline';";

  if (isUsingDesiredCsp) {
    tabsUsingDesiredCsp.set(tabId, url);
  } else {
    tabsUsingDesiredCsp.delete(tabId);
  }

  setIconForTab(tabId, url);
}

chrome.webRequest.onHeadersReceived.addListener(
  requestProcessor,
  {
    urls: ['<all_urls>'],
    types: ['main_frame'],
  },
  ['responseHeaders']
);
