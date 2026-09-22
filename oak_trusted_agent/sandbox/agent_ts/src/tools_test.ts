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
import type { ToolDescription } from 'oak:agent/tools@0.1.0';
import { HostToolRegistry, WitTools } from './tools';

interface MockToolSpec {
  name: string;
  description: string;
  // WIT `tool-description` passes `input-schema` as a JSON-encoded string
  // across the Wasm boundary; allow object literals here for readability.
  inputSchema: Record<string, unknown> | string;
}

function toWitToolDescription(spec: MockToolSpec): ToolDescription {
  return {
    name: spec.name,
    description: spec.description,
    inputSchema:
      typeof spec.inputSchema === 'string'
        ? spec.inputSchema
        : JSON.stringify(spec.inputSchema),
  };
}

function createMockWitTools(initialTools?: MockToolSpec[]): {
  witTools: WitTools;
  setTools: (tools: MockToolSpec[]) => void;
} {
  let currentTools: MockToolSpec[] = initialTools ?? [
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

  return {
    witTools: {
      listTools: () => currentTools.map(toWitToolDescription),
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
        if (name === 'get_current_time') {
          return JSON.stringify({
            unix_timestamp: 1775000000,
          });
        }
        return `Raw string result from ${name}`;
      },
    },
    setTools: (tools: MockToolSpec[]) => {
      currentTools = [...tools];
    },
  };
}

describe('HostToolRegistry', () => {
  it('discovers and invokes host tools and supports dynamic tool addition', () => {
    const { witTools, setTools } = createMockWitTools();
    const registry = new HostToolRegistry(witTools);

    const tools = registry.listTools();
    assert.equal(tools.length, 2);
    assert.equal(tools[0].name, 'get_weather');

    const weatherResult = registry.call('get_weather', {
      location: 'New York',
    }) as Record<string, unknown>;
    assert.equal(weatherResult.location, 'New York');
    assert.equal(weatherResult.conditions, 'Sunny');

    // Verify dynamic tool discovery when host adds a new tool at runtime
    setTools([
      ...tools,
      {
        name: 'dynamic_tool',
        description: 'Dynamically registered host tool',
        inputSchema: {},
      },
    ]);

    const dynamicTool = registry.getTool('dynamic_tool');
    assert.ok(dynamicTool !== undefined);
    const rawResult = registry.call('dynamic_tool', {});
    assert.equal(rawResult, 'Raw string result from dynamic_tool');

    assert.throws(() => {
      registry.call('unknown_tool', {});
    }, /Tool 'unknown_tool' not found in registry/);
  });

  it('throws an error when a tool has invalid JSON in inputSchema', () => {
    const { witTools } = createMockWitTools([
      {
        name: 'broken_tool',
        description: 'Tool with malformed JSON schema',
        inputSchema: '{invalid-json',
      },
    ]);
    const registry = new HostToolRegistry(witTools);

    assert.throws(() => {
      registry.listTools();
    }, SyntaxError);
  });
});
