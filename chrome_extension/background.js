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

// TODO(#1492): Generate an ECDSA key pair, and use the private key for authentication and the
// public key as Oak label.
//
// See https://developer.mozilla.org/en-US/docs/Web/API/SubtleCrypto/sign

// Ids of tabs that have entered Oak mode.
const enabledTabs = new Set();

// Intercept outgoing requests, and block them if they are coming from a tab that has entered Oak
// mode.
//
// TODO(#1492): This only intercepts new WebSocket connections, but not individual messages on
// previously established connections. e.g. https://www.websocket.org/echo.html.
//
// TODO(#1492): This does not catch cases in which a tab opens another tab via JavaScript, e.g.
// `window.open('https://google.com/?q=123');`.
chrome.webRequest.onBeforeRequest.addListener(
  (details) => {
    const tabId = details.tabId;
    const oakMode = enabledTabs.has(tabId);
    console.log(
      'request from tab ' + tabId + ': ' + (oakMode ? 'blocked' : 'allowed')
    );
    // For now, we just cancel all outgoing requests once a tab has entered Oak mode, which is not
    // particularly meaningful (and in fact quite annoying, since it is irreversible). But this serves
    // as a proof of concepts that we can intercept requests and block them with arbitrary logic.
    //
    // TODO(#1492): Instead of just cancelling all requests, we should allow Oak requests through,
    // and attach authentication credentials and labels to them. For this, we need to determine
    // which ones are legitimate Oak requests though.
    return { cancel: oakMode };
  },
  // filters
  { urls: ['<all_urls>'] },
  // extraInfoSpec
  ['blocking']
);

// Listen for messages from `content.js` that signal whether to enable Oak mode for a specific tab.
chrome.runtime.onMessage.addListener((message, sender) => {
  console.log('message received', message, sender);
  if (message == 'oak_enter') {
    const tabId = sender.tab.id;
    console.log('entering Oak mode for tab ' + tabId);
    enabledTabs.add(tabId);
  }
});
