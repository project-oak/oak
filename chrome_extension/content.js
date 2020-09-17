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

// The extension id assigned by Chrome to this extension.
const extensionId = 'nimjbbjddomejdcjaobokgnfmjgjefcc';

// Listen for messages from the top frame of the current tab.
//
// This may be sent with something similar to the following:
//
// ```
// window.postMessage('oak_enter');
// ```
//
// Once this content script receives such message, then it sends in turn a message to the background
// script of the extension.
window.addEventListener(
  'message',
  (event) => {
    console.log('message received', event);
    if (event.data == 'oak_enter') {
      chrome.runtime.sendMessage(extensionId, 'oak_enter');
    }
  },
  false
);
