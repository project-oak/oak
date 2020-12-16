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

const showGreenIconForExtensionPages = {
  conditions: [
    new chrome.declarativeContent.PageStateMatcher({
      pageUrl: {
        hostEquals: chrome.runtime.id,
        schemes: ['chrome-extension'],
        pathEquals: '/index.html',
      },
    }),
  ],
  actions: [new chrome.declarativeContent.SetIcon({ path: 'icon-green.png' })],
};

chrome.runtime.onInstalled.addListener(function () {
  chrome.declarativeContent.onPageChanged.removeRules(undefined, function () {
    chrome.declarativeContent.onPageChanged.addRules([
      showGreenIconForExtensionPages,
    ]);
  });
});

async function loadPageInASecureSandbox({ id: tabId }) {
  const src = (
    await new Promise((resolve) =>
      chrome.tabs.executeScript(tabId, { file: 'getInnerHtml.js' }, resolve)
    )
  )?.[0];

  // It's possible that the chrome extension cannot read the source code, either
  // because it is served via a non-permitted scheme (eg `chrome-extension://`),
  // or bc the user/adminstrator has denied this extension access to the page.
  if (!src) {
    chrome.notifications.create(undefined, {
      type: 'basic',
      title: 'Could not sandbox this page',
      message: 'The extension does not have permission to modify this page.',
      iconUrl: 'icon-red.png',
      isClickable: false,
      eventTime: Date.now(),
    });
    return;
  }

  const searchParams = new URLSearchParams({ src });
  const url = `index.html?${searchParams.toString()}`;
  chrome.tabs.update({ url });
}

chrome.browserAction.onClicked.addListener(loadPageInASecureSandbox);
