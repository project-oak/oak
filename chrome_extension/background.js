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

const isUsingDesiredCspPerTab = new Map();

function setIconForTab(tabId) {
  const isUsingDesiredCsp = isUsingDesiredCspPerTab.get(tabId);

  chrome.browserAction.setIcon({
    path: isUsingDesiredCsp ? GREEN_ICON_PATH : RED_ICON_PATH,
    tabId,
  });
}

chrome.tabs.onUpdated.addListener(setIconForTab);
chrome.tabs.onRemoved.addListener(isUsingDesiredCspPerTab.delete);

function requestProcessor({ responseHeaders, tabId }) {
  const cspHeader = responseHeaders.find(
    (header) => header.name.toLowerCase() === 'content-security-policy'
  );

  // TODO(#1492): Parse the CSP to check whether it is as strict or stricter
  // than the minimum CSP, instead of just checking if the string matches.
  const isUsingDesiredCsp =
    cspHeader !== undefined &&
    cspHeader.value ===
      "default-src 'none'; sandbox allow-scripts; script-src 'unsafe-inline'; style-src 'unsafe-inline';";

  isUsingDesiredCspPerTab.set(tabId, isUsingDesiredCsp);

  setIconForTab(tabId);
}

chrome.webRequest.onHeadersReceived.addListener(
  requestProcessor,
  {
    urls: ['<all_urls>'],
    types: ['main_frame'],
  },
  ['responseHeaders']
);
