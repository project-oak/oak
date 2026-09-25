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
import {
  BaseLlm,
  BaseLlmConnection,
  LlmRequest,
  LlmResponse,
} from '@google/adk';
import { TrustedAgent } from './agent';
import { OakModel, WitModel } from './models';
import { OakToolset, WitTools } from './tools';

/**
 * Deterministic test BaseLlm implementation for hermetic agent loop tests.
 */
class MockAdkModel extends BaseLlm {
  constructor() {
    super({ model: 'mock-model' });
  }

  override async *generateContentAsync(
    llmRequest: LlmRequest,
  ): AsyncGenerator<LlmResponse, void> {
    const contents = llmRequest.contents || [];
    let prompt = '';
    let lastFunctionResponse: Record<string, unknown> | undefined;

    for (const c of contents) {
      for (const p of c.parts || []) {
        if (p.text && c.role === 'user' && !prompt) {
          prompt = p.text;
        }
        if (p.functionResponse) {
          lastFunctionResponse = p.functionResponse.response;
        }
      }
    }

    if (lastFunctionResponse) {
      const loc = String(lastFunctionResponse.location || 'San Francisco');
      const cond = String(lastFunctionResponse.conditions || 'Sunny');
      const temp = String(lastFunctionResponse.temperature || '21°C');
      const hum = String(lastFunctionResponse.humidity || '45%');
      const src = String(
        lastFunctionResponse.source || 'Oak Attested Weather Service',
      );
      yield {
        content: {
          role: 'model',
          parts: [
            {
              text: 'I have received the weather observation from the Oak Attested Weather Service. Synthesizing final answer.',
              thought: true,
            },
            {
              text: `The weather in ${loc} is currently ${cond} with a temperature of ${temp} and humidity at ${hum} (attested by ${src}).`,
            },
          ],
        },
      };
      return;
    }

    if (prompt.toLowerCase().includes('weather')) {
      yield {
        content: {
          role: 'model',
          parts: [
            {
              text: "User is requesting weather information. Selecting 'get_weather' tool for San Francisco.",
              thought: true,
            },
            {
              functionCall: {
                name: 'get_weather',
                args: { location: 'San Francisco' },
              },
            },
          ],
        },
      };
      return;
    }

    yield {
      content: {
        role: 'model',
        parts: [
          {
            text: 'Hello! I am an Oak Trusted Agent implemented with Google ADK in TypeScript running inside an attested WebAssembly sandbox.',
          },
        ],
      },
    };
  }

  override async connect(_llmRequest: LlmRequest): Promise<BaseLlmConnection> {
    throw new Error('Live streaming connections are not supported in sandbox');
  }
}

function createMockToolset(): OakToolset {
  const mockToolSpecs = [
    {
      name: 'get_weather',
      description: 'Returns attested weather conditions for a city',
      inputSchema: {
        type: 'object',
        properties: { location: { type: 'string' } },
        required: ['location'],
      },
    },
    {
      name: 'get_current_time',
      description: 'Returns the synchronized host UTC timestamp',
      inputSchema: { type: 'object', properties: {} },
    },
  ];

  const witTools: WitTools = {
    listTools: () =>
      mockToolSpecs.map((spec) => ({
        name: spec.name,
        description: spec.description,
        inputSchema: JSON.stringify(spec.inputSchema),
      })),
    callTool: (name: string, args: string): string => {
      const parsedArgs = JSON.parse(args || '{}') as Record<string, unknown>;
      if (name === 'get_weather') {
        return JSON.stringify({
          location: parsedArgs.location || 'San Francisco',
          conditions: 'Sunny',
          temperature: '21°C',
          humidity: '45%',
          source: 'Oak Attested Weather Service',
        });
      }
      return JSON.stringify({ unix_timestamp: 1775000000 });
    },
  };
  return new OakToolset(witTools);
}

describe('TrustedAgent', () => {
  it('executes the tool call and observation loop', async () => {
    const agent = new TrustedAgent({
      name: 'test_agent',
      maxSteps: 4,
      model: new MockAdkModel(),
      toolset: createMockToolset(),
    });

    const weatherTrace = await agent.run(
      'What is the weather in San Francisco?',
    );
    assert.ok(weatherTrace.includes('=== Agent Session: test_agent ==='));
    assert.ok(weatherTrace.includes("[Tool Call] Invoking 'get_weather'"));
    assert.ok(
      weatherTrace.includes('[Observation] {"location":"San Francisco"'),
    );
    assert.ok(
      weatherTrace.includes(
        '[Final Answer] The weather in San Francisco is currently Sunny',
      ),
    );
  });

  it('captures tool execution errors gracefully in the trace', async () => {
    class ErrorTestModel extends BaseLlm {
      private step = 0;
      constructor() {
        super({ model: 'error-model' });
      }
      override async *generateContentAsync(): AsyncGenerator<
        LlmResponse,
        void
      > {
        this.step++;
        if (this.step === 1) {
          yield {
            content: {
              role: 'model',
              parts: [
                { text: 'Calling nonexistent tool', thought: true },
                { functionCall: { name: 'missing_tool', args: {} } },
              ],
            },
          };
        } else {
          yield {
            content: {
              role: 'model',
              parts: [{ text: 'Recovered from tool error' }],
            },
          };
        }
      }
      override async connect(): Promise<BaseLlmConnection> {
        throw new Error('unsupported');
      }
    }

    const errorAgent = new TrustedAgent({
      name: 'error_test_agent',
      maxSteps: 2,
      toolset: createMockToolset(),
      model: new ErrorTestModel(),
    });

    const errorTrace = await errorAgent.run('Trigger tool error');
    assert.ok(
      errorTrace.includes(
        '[Tool Error] Function missing_tool is not found in the toolsDict.',
      ),
    );
    assert.ok(errorTrace.includes('[Final Answer] Recovered from tool error'));
  });

  it('forwards ADK tool declarations when using OakModel', async () => {
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
            },
          ],
        });
      },
    };

    const model = new OakModel(mockWitModel);
    const liveAgent = new TrustedAgent({
      name: 'live_proxy_agent',
      model,
      toolset: createMockToolset(),
    });
    const liveTrace = await liveAgent.run('Hello via host model');
    const parsedBody = JSON.parse(capturedRequest) as Record<string, unknown>;
    assert.ok(Array.isArray(parsedBody.tools) && parsedBody.tools.length > 0);
    assert.ok(
      liveTrace.includes('[Final Answer] Attested response from host model'),
    );
  });
});
