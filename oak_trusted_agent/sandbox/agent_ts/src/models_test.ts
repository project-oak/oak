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
import { LlmRequest } from '@google/adk';
import { OakModel, WitModel } from './models';

describe('OakModel', () => {
  it('forwards generateContent requests with model info from getModelInfo()', async () => {
    let capturedRequest = '';

    const mockWitModel: WitModel = {
      getModelInfo: () => ({
        name: 'gemma4:e2b-it-qat',
        provider: 'ollama',
      }),
      callModel: (request: string): string => {
        capturedRequest = request;
        return JSON.stringify({
          candidates: [
            {
              content: {
                parts: [{ text: 'Attested response from host model' }],
              },
              finishReason: 'STOP',
            },
          ],
        });
      },
    };

    const model = new OakModel(mockWitModel);
    const llmRequest = {
      contents: [
        { role: 'user', parts: [{ text: 'Summarize security properties' }] },
      ],
    } as LlmRequest;

    const responses = [];
    for await (const resp of model.generateContentAsync(llmRequest)) {
      responses.push(resp);
    }

    assert.equal(responses.length, 1);
    assert.equal(
      responses[0].content?.parts?.[0]?.text,
      'Attested response from host model',
    );

    const parsedRequest = JSON.parse(capturedRequest) as Record<
      string,
      unknown
    >;
    assert.equal(parsedRequest.model, 'gemma4:e2b-it-qat');
    assert.equal(parsedRequest.provider, 'ollama');
    assert.ok(Array.isArray(parsedRequest.contents));
  });

  it('handles safety finishReason when candidate contains no parts', async () => {
    const mockWitModel: WitModel = {
      getModelInfo: () => ({
        name: 'gemma4:e2b-it-qat',
        provider: 'ollama',
      }),
      callModel: (): string => {
        return JSON.stringify({
          candidates: [
            {
              content: { parts: [] },
              finishReason: 'SAFETY',
              finishMessage: 'Response blocked for safety reasons',
            },
          ],
        });
      },
    };

    const model = new OakModel(mockWitModel);
    const llmRequest = {
      contents: [{ role: 'user', parts: [{ text: 'Blocked prompt test' }] }],
    } as LlmRequest;

    const responses = [];
    for await (const resp of model.generateContentAsync(llmRequest)) {
      responses.push(resp);
    }

    assert.equal(responses.length, 1);
    assert.equal(
      responses[0].errorMessage,
      'Response blocked for safety reasons',
    );
    assert.equal(responses[0].finishReason, 'SAFETY');
    assert.ok(
      responses[0].content?.parts?.[0]?.text?.includes(
        '[Generation stopped: SAFETY]',
      ),
    );
  });

  it('handles blocked prompt in promptFeedback', async () => {
    const mockWitModel: WitModel = {
      getModelInfo: () => ({
        name: 'gemma4:e2b-it-qat',
        provider: 'gemini',
      }),
      callModel: (): string => {
        return JSON.stringify({
          promptFeedback: {
            blockReason: 'PROHIBITED_CONTENT',
            blockReasonMessage: 'Content violates usage guidelines',
          },
        });
      },
    };

    const model = new OakModel(mockWitModel);
    const llmRequest = {
      contents: [{ role: 'user', parts: [{ text: 'Prohibited prompt test' }] }],
    } as LlmRequest;

    const responses = [];
    for await (const resp of model.generateContentAsync(llmRequest)) {
      responses.push(resp);
    }

    assert.equal(responses.length, 1);
    assert.equal(
      responses[0].errorMessage,
      'Model prompt blocked: PROHIBITED_CONTENT',
    );
    assert.ok(
      responses[0].content?.parts?.[0]?.text?.includes(
        '[Blocked: PROHIBITED_CONTENT]',
      ),
    );
  });

  it('propagates host model errors when callModel throws', async () => {
    const mockWitModel: WitModel = {
      getModelInfo: () => ({
        name: 'gemma4:e2b-it-qat',
        provider: 'ollama',
      }),
      callModel: (): string => {
        throw new Error('Host model execution failed: 503 Service Unavailable');
      },
    };

    const model = new OakModel(mockWitModel);
    const llmRequest = {
      contents: [{ role: 'user', parts: [{ text: 'Test failure' }] }],
    } as LlmRequest;

    await assert.rejects(async () => {
      // eslint-disable-next-line @typescript-eslint/no-unused-vars
      for await (const _ of model.generateContentAsync(llmRequest)) {
        // should throw
      }
    }, /503 Service Unavailable/);
  });
});
