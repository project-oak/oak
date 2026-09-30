// Copyright 2026 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

import { readFile } from 'node:fs/promises';

export default {
  plugins: [
    {
      name: 'starlingmonkey-unicode-regex',
      setup(build) {
        // StarlingMonkey (embedded in componentize-js) omits ICU Unicode property tables;
        // normalize the ASCII identifier regex in @google/adk before Wizer pre-initialization.
        build.onLoad({ filter: /index_web\.js$/ }, async (args) => {
          const source = await readFile(args.path, 'utf8');
          return {
            contents: source
              .replace(/\\p\{ID_Start\}/g, 'a-zA-Z')
              .replace(/\\p\{ID_Continue\}/g, 'a-zA-Z0-9'),
            loader: 'js',
          };
        });
      },
    },
  ],
};
