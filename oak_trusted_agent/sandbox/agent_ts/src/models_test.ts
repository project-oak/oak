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

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { OllamaWasiModel } from './models';

describe('OllamaWasiModel', () => {
  it('sends generateContent requests without raw API key headers', async (t) => {
    let capturedUrl = '';
    let capturedInit: RequestInit | undefined;

    t.mock.method(
      globalThis,
      'fetch',
      async (
        input: RequestInfo | URL,
        init?: RequestInit,
      ): Promise<Response> => {
        capturedUrl = String(input);
        capturedInit = init;
        return {
          ok: true,
          status: 200,
          statusText: 'OK',
          json: async () => ({
            candidates: [
              {
                content: {
                  parts: [{ text: 'Attested response from Ollama proxy' }],
                },
              },
            ],
          }),
        } as Response;
      },
    );

    const model = new OllamaWasiModel(
      'http://127.0.0.1:8080',
      'gemma4:e2b-it-qat',
    );
    const response = await model.generate('Summarize security properties', [
      { role: 'user', content: 'Previous turn' },
    ]);

    assert.equal(
      capturedUrl,
      'http://127.0.0.1:8080/v1beta/models/gemma4:e2b-it-qat:generateContent',
    );
    const headers = (capturedInit?.headers || {}) as Record<string, string>;
    assert.equal(headers['Content-Type'], 'application/json');
    assert.equal(headers['x-goog-api-key'], undefined);
    assert.equal(response.finalAnswer, 'Attested response from Ollama proxy');
  });

  it('throws an Error on non-OK HTTP status', async (t) => {
    t.mock.method(globalThis, 'fetch', async (): Promise<Response> => {
      return {
        ok: false,
        status: 503,
        statusText: 'Service Unavailable',
      } as Response;
    });

    const model = new OllamaWasiModel(
      'http://127.0.0.1:8080',
      'gemma4:e2b-it-qat',
    );
    await assert.rejects(async () => {
      await model.generate('Test HTTP failure', []);
    }, /503 Service Unavailable/);
  });
});
