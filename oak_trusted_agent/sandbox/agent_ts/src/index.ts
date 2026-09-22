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

import * as witTools from 'oak:agent/tools@0.1.0';
import { TrustedAgent } from './agent';
import { OllamaWasiModel } from './models';
import { HostToolRegistry } from './tools';

const trustedAgent = new TrustedAgent({
  model: new OllamaWasiModel(),
  toolRegistry: new HostToolRegistry(witTools),
});

/**
 * WebAssembly Component Model export for world oak:agent/oak-agent@0.1.0
 */
export const agent = {
  async run(userMessage: string): Promise<string> {
    return await trustedAgent.run(userMessage);
  },
};
