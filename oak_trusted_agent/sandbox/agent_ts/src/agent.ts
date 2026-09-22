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

import {
  BaseLlm,
  BaseLlmConnection,
  InMemoryRunner,
  LlmAgent,
  LlmRequest,
  LlmResponse,
} from '@google/adk';
import { HistoryItem, Model, ModelResponse } from './models';
import { HostToolRegistry } from './tools';

type Part = NonNullable<NonNullable<LlmResponse['content']>['parts']>[number];

export interface AgentConfig {
  name?: string;
  instruction?: string;
  model: Model | BaseLlm;
  toolRegistry?: HostToolRegistry;
  maxSteps?: number;
}

/**
 * Google ADK Agent (`LlmAgent` + `InMemoryRunner`) running inside an attested
 * WebAssembly sandbox.
 */
export class TrustedAgent {
  public readonly name: string;
  public readonly instruction: string;
  public readonly toolRegistry: HostToolRegistry;
  public readonly model: BaseLlm;
  public readonly maxSteps: number;
  public readonly llmAgent: LlmAgent;

  constructor(config: AgentConfig) {
    this.name = config.name || 'oak_trusted_agent_ts';
    this.instruction =
      config.instruction ||
      'You are an Oak Trusted Agent running inside an attested WebAssembly sandbox. Use available tools to answer user questions truthfully and securely.';
    this.toolRegistry =
      config.toolRegistry ??
      new HostToolRegistry({
        listTools: () => [],
        callTool: () => {
          throw new Error('No host tools configured');
        },
      });
    if (!config.model) {
      throw new Error('A model must be provided in AgentConfig.');
    } else if (config.model instanceof BaseLlm) {
      this.model = config.model;
    } else {
      this.model = new ModelAdapter(config.model);
    }
    this.maxSteps = config.maxSteps || 5;

    this.llmAgent = new LlmAgent({
      name: this.name,
      instruction: this.instruction,
      model: this.model,
      tools: [this.toolRegistry],
    });
  }

  /**
   * Executes the Google ADK `InMemoryRunner` session loop for a user message.
   */
  public async run(userMessage: string): Promise<string> {
    const traceLogs: string[] = [];

    traceLogs.push(`=== Agent Session: ${this.name} ===`);
    traceLogs.push(`[Preamble] ${this.instruction}`);
    traceLogs.push(
      `[Available Tools] ${this.toolRegistry
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

/**
 * Adapter wrapping a plain `Model` interface as an ADK `BaseLlm` instance.
 */
class ModelAdapter extends BaseLlm {
  private readonly delegate: Model;

  constructor(delegate: Model) {
    super({ model: 'custom-model' });
    this.delegate = delegate;
  }

  override async *generateContentAsync(
    llmRequest: LlmRequest,
  ): AsyncGenerator<LlmResponse, void> {
    let prompt = '';
    const history: HistoryItem[] = [];

    for (const content of llmRequest.contents || []) {
      for (const part of content.parts || []) {
        if (part.functionResponse) {
          const respObj = part.functionResponse.response || {};
          history.push({
            role: 'tool',
            content: JSON.stringify(respObj),
          });
        } else if (part.text) {
          if (content.role === 'user' && !prompt) {
            prompt = part.text;
          } else {
            history.push({
              role: content.role === 'model' ? 'model' : 'user',
              content: part.text,
            });
          }
        }
      }
    }

    const step: ModelResponse = await this.delegate.generate(prompt, history);
    const parts: Part[] = [];
    if (step.thought) {
      parts.push({ text: step.thought, thought: true });
    }
    if (step.toolCall) {
      parts.push({
        functionCall: {
          name: step.toolCall.name,
          args: step.toolCall.args,
        },
      });
    } else if (step.finalAnswer) {
      parts.push({ text: step.finalAnswer });
    }

    yield {
      content: {
        role: 'model',
        parts,
      },
    };
  }

  override async connect(_llmRequest: LlmRequest): Promise<BaseLlmConnection> {
    throw new Error('Live streaming connections are not supported in sandbox');
  }
}
