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
import { TrustedAgent } from './agent';
import { HistoryItem, Model, ModelResponse, OllamaWasiModel } from './models';
import { HostToolRegistry, WitTools } from './tools';

/**
 * Deterministic test model implementation for hermetic agent loop tests.
 */
class MockAdkModel implements Model {
  public generate(prompt: string, history: HistoryItem[]): ModelResponse {
    const lastToolItem = [...history]
      .reverse()
      .find((item) => item.role === 'tool');

    if (lastToolItem) {
      const observation = JSON.parse(lastToolItem.content) as Record<
        string,
        unknown
      >;
      if (observation.source || observation.conditions) {
        const loc = String(observation.location || 'San Francisco');
        const cond = String(observation.conditions || 'Sunny');
        const temp = String(observation.temperature || '21°C');
        const hum = String(observation.humidity || '45%');
        const src = String(
          observation.source || 'Oak Attested Weather Service',
        );
        return {
          thought:
            'I have received the weather observation from the Oak Attested Weather Service. Synthesizing final answer.',
          finalAnswer: `The weather in ${loc} is currently ${cond} with a temperature of ${temp} and humidity at ${hum} (attested by ${src}).`,
        };
      }
      return {
        thought: 'Tool execution completed successfully.',
        finalAnswer: `Tool result: ${JSON.stringify(observation)}`,
      };
    }

    if (prompt.toLowerCase().includes('weather')) {
      return {
        thought:
          "User is requesting weather information. Selecting 'get_weather' tool for San Francisco.",
        toolCall: {
          name: 'get_weather',
          args: { location: 'San Francisco' },
        },
      };
    }

    return {
      thought:
        'General query received without tool requirement. Responding directly.',
      finalAnswer:
        'Hello! I am an Oak Trusted Agent implemented with Google ADK in TypeScript running inside an attested WebAssembly sandbox.',
    };
  }
}

function createMockToolRegistry(): HostToolRegistry {
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
  return new HostToolRegistry(witTools);
}

describe('TrustedAgent', () => {
  it('executes the tool call and observation loop', async () => {
    const agent = new TrustedAgent({
      name: 'test_agent',
      maxSteps: 4,
      model: new MockAdkModel(),
      toolRegistry: createMockToolRegistry(),
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
    let step = 0;
    const errorAgent = new TrustedAgent({
      name: 'error_test_agent',
      maxSteps: 2,
      toolRegistry: createMockToolRegistry(),
      model: {
        generate: () => {
          step++;
          if (step === 1) {
            return {
              thought: 'Calling nonexistent tool',
              toolCall: { name: 'missing_tool', args: {} },
            };
          }
          return {
            finalAnswer: 'Recovered from tool error',
          };
        },
      },
    });

    const errorTrace = await errorAgent.run('Trigger tool error');
    assert.ok(
      errorTrace.includes(
        '[Tool Error] Function missing_tool is not found in the toolsDict.',
      ),
    );
    assert.ok(errorTrace.includes('[Final Answer] Recovered from tool error'));
  });

  it('forwards ADK tool declarations when using OllamaWasiModel', async (t) => {
    let capturedInit: RequestInit | undefined;

    t.mock.method(
      globalThis,
      'fetch',
      async (
        _input: RequestInfo | URL,
        init?: RequestInit,
      ): Promise<Response> => {
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
    const liveAgent = new TrustedAgent({
      name: 'live_proxy_agent',
      model,
      toolRegistry: createMockToolRegistry(),
    });
    const liveTrace = await liveAgent.run('Hello via host proxy');
    const parsedBody = JSON.parse(String(capturedInit?.body || '{}')) as Record<
      string,
      unknown
    >;
    assert.ok(Array.isArray(parsedBody.tools) && parsedBody.tools.length > 0);
    assert.ok(
      liveTrace.includes('[Final Answer] Attested response from Ollama proxy'),
    );
  });
});
