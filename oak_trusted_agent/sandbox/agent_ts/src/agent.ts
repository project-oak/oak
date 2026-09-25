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

import { BaseLlm, InMemoryRunner, LlmAgent } from '@google/adk';
import { OakToolset } from './tools';

export interface AgentConfig {
  name?: string;
  instruction?: string;
  model: BaseLlm;
  toolset?: OakToolset;
  toolRegistry?: OakToolset;
  maxSteps?: number;
}

/**
 * Google ADK Agent (`LlmAgent` + `InMemoryRunner`) running inside an attested
 * WebAssembly sandbox.
 */
export class TrustedAgent {
  public readonly name: string;
  public readonly instruction: string;
  public readonly toolset: OakToolset;
  public readonly model: BaseLlm;
  public readonly maxSteps: number;
  public readonly llmAgent: LlmAgent;

  constructor(config: AgentConfig) {
    this.name = config.name || 'oak_trusted_agent_ts';
    this.instruction =
      config.instruction ||
      'You are an Oak Trusted Agent running inside an attested WebAssembly sandbox. Use available tools to answer user questions truthfully and securely.';
    this.toolset =
      config.toolset ??
      config.toolRegistry ??
      new OakToolset({
        listTools: () => [],
        callTool: () => {
          throw new Error('No host tools configured');
        },
      });
    if (!config.model) {
      throw new Error('A model must be provided in AgentConfig.');
    }
    this.model = config.model;
    this.maxSteps = config.maxSteps || 5;

    this.llmAgent = new LlmAgent({
      name: this.name,
      instruction: this.instruction,
      model: this.model,
      tools: [this.toolset],
    });
  }

  public get toolRegistry(): OakToolset {
    return this.toolset;
  }

  /**
   * Executes the Google ADK `InMemoryRunner` session loop for a user message.
   */
  public async run(userMessage: string): Promise<string> {
    const traceLogs: string[] = [];

    traceLogs.push(`=== Agent Session: ${this.name} ===`);
    traceLogs.push(`[Preamble] ${this.instruction}`);
    traceLogs.push(
      `[Available Tools] ${this.toolset
        .listTools()
        .map((t) => t.name)
        .join(', ')}`,
    );
    traceLogs.push(`[User Prompt] "${userMessage}"`);
    traceLogs.push('--------------------------------------');

    const runner = new InMemoryRunner({
      agent: this.llmAgent,
      appName: this.name,
    });

    let currentStep = 0;
    for await (const event of runner.runEphemeral({
      userId: 'sandbox_user',
      newMessage: {
        role: 'user',
        parts: [{ text: userMessage }],
      },
      runConfig: {
        maxLlmCalls: this.maxSteps,
      },
    })) {
      for (const part of event?.content?.parts || []) {
        if (part.thought && part.text) {
          currentStep++;
          traceLogs.push(`[Step ${currentStep} Thought] ${part.text}`);
        } else if (part.functionCall) {
          const { name, args } = part.functionCall;
          traceLogs.push(
            `[Tool Call] Invoking '${name}' with args: ${JSON.stringify(args || {})}`,
          );
        } else if (part.functionResponse) {
          const resp = part.functionResponse.response;
          if (resp?.error) {
            traceLogs.push(`[Tool Error] ${String(resp.error)}`);
          } else {
            traceLogs.push(`[Observation] ${JSON.stringify(resp)}`);
          }
        } else if (part.text) {
          traceLogs.push(`[Final Answer] ${part.text}`);
        }
      }
    }

    traceLogs.push('======================================');
    return traceLogs.join('\n');
  }
}
