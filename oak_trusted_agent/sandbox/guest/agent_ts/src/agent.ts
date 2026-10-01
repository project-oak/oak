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
import { logger } from './logger';
import { OakToolset } from './tools';

const USER_ID = 'sandbox_user';

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
 *
 * Successive `run` calls are turns of a single conversation: the agent keeps
 * an in-memory ADK session for as long as it lives, which is the lifetime of
 * the sandbox instance.
 */
export class TrustedAgent {
  public readonly name: string;
  public readonly instruction: string;
  public readonly toolset: OakToolset;
  public readonly model: BaseLlm;
  public readonly maxSteps: number;
  public readonly llmAgent: LlmAgent;
  private readonly runner: InMemoryRunner;
  private sessionId?: string;

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
    this.runner = new InMemoryRunner({
      agent: this.llmAgent,
      appName: this.name,
    });
  }

  public get toolRegistry(): OakToolset {
    return this.toolset;
  }

  /**
   * Executes the Google ADK `InMemoryRunner` session loop for a user message,
   * as the next turn of the agent's conversation.
   *
   * Intermediate execution events (thoughts, tool calls, observations) are logged
   * via `loglevel` (which prints to stdout in debug/insecure mode and is safely suppressed
   * when stdio is disabled in secure mode).
   *
   * Only the agent's final answer is returned to the user.
   */
  public async run(userMessage: string): Promise<string> {
    logger.info(`=== Agent Session: ${this.name} ===`);
    logger.debug(`[Preamble] ${this.instruction}`);
    logger.debug(
      `[Available Tools] ${this.toolset
        .listTools()
        .map((t) => t.name)
        .join(', ')}`,
    );
    logger.info(`[User Prompt] "${userMessage}"`);

    if (this.sessionId === undefined) {
      const session = await this.runner.sessionService.createSession({
        appName: this.name,
        userId: USER_ID,
      });
      this.sessionId = session.id;
    }

    let currentStep = 0;
    const finalAnswerParts: string[] = [];

    for await (const event of this.runner.runAsync({
      userId: USER_ID,
      sessionId: this.sessionId,
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
          logger.debug(`[Step ${currentStep} Thought] ${part.text}`);
        } else if (part.functionCall) {
          const { name, args } = part.functionCall;
          logger.info(
            `[Tool Call] Invoking '${name}' with args: ${JSON.stringify(args || {})}`,
          );
        } else if (part.functionResponse) {
          const resp = part.functionResponse.response;
          if (resp?.error) {
            logger.error(`[Tool Error] ${String(resp.error)}`);
          } else {
            logger.info(`[Observation] ${JSON.stringify(resp)}`);
          }
        } else if (part.text) {
          logger.info(`[Final Answer] ${part.text}`);
          finalAnswerParts.push(part.text);
        }
      }
    }

    logger.info('======================================');
    return finalAnswerParts.join('\n');
  }
}
