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

/**
 * Google ADK BaseLlm implementations for the TypeScript ADK Agent.
 * Dispatches model execution requests to the host across the WIT
 * boundary (oak:agent/model@0.1.0). The host provides model metadata
 * via getModelInfo() and issues the actual model calls on behalf of the sandbox.
 */

import {
  BaseLlm,
  BaseLlmConnection,
  LlmRequest,
  LlmResponse,
} from '@google/adk';
import type { ModelInfo, ModelProvider } from 'oak:agent/model@0.1.0';

type Content = NonNullable<LlmResponse['content']>;

export interface GenerateContentApiResponse {
  candidates?: Array<{
    content?: Content;
    finishReason?: string;
    finishMessage?: string;
  }>;
  promptFeedback?: {
    blockReason?: string;
    blockReasonMessage?: string;
  };
}

/**
 * Interface representing the WIT `oak:agent/model@0.1.0` host import module.
 * Across the WebAssembly Component Model boundary, the host exposes model
 * configuration via `getModelInfo` and processes model execution requests via `callModel`.
 */
export interface WitModel {
  getModelInfo(): ModelInfo;
  callModel(request: string): string;
}

export type { ModelInfo, ModelProvider };

/**
 * Google ADK BaseLlm implementation targeting the host model provider
 * across the WIT `oak:agent/model@0.1.0` interface.
 */
export class OakModel extends BaseLlm {
  private readonly witModel: WitModel;
  private modelInfo?: ModelInfo;

  constructor(witModel: WitModel) {
    super({ model: 'oak-model' });
    this.witModel = witModel;
  }

  public getModelInfo(): ModelInfo {
    if (!this.modelInfo) {
      this.modelInfo = this.witModel.getModelInfo();
    }
    return this.modelInfo;
  }

  override async *generateContentAsync(
    llmRequest: LlmRequest,
  ): AsyncGenerator<LlmResponse, void> {
    const info = this.getModelInfo();
    const requestBody: Record<string, unknown> = {
      model: info.name,
      provider: info.provider,
      contents: llmRequest.contents,
    };
    if (llmRequest.config?.systemInstruction) {
      requestBody.systemInstruction = llmRequest.config.systemInstruction;
    }
    if (llmRequest.config?.tools) {
      requestBody.tools = llmRequest.config.tools;
    }

    const rawResult = this.witModel.callModel(JSON.stringify(requestBody));
    let data: GenerateContentApiResponse;
    try {
      data = JSON.parse(rawResult) as GenerateContentApiResponse;
    } catch (e) {
      yield {
        content: { role: 'model', parts: [] },
        errorMessage: `Failed to parse host model response as JSON: ${e}`,
      };
      return;
    }

    if (data.promptFeedback?.blockReason) {
      const reason = data.promptFeedback.blockReason;
      const msg =
        data.promptFeedback.blockReasonMessage ||
        'Prompt was blocked by safety filters';
      yield {
        content: {
          role: 'model',
          parts: [{ text: `[Blocked: ${reason}] ${msg}` }],
        },
        errorMessage: `Model prompt blocked: ${reason}`,
      };
      return;
    }

    const candidate = data.candidates?.[0];
    if (!candidate) {
      yield {
        content: { role: 'model', parts: [] },
        errorMessage: 'Model returned no candidate answers.',
      };
      return;
    }

    const candidateContent = candidate.content;
    const finishReason = candidate.finishReason;

    // Handle case where call succeeds but contains no answer (e.g. SAFETY, MAX_TOKENS)
    if (
      (!candidateContent?.parts || candidateContent.parts.length === 0) &&
      finishReason &&
      finishReason !== 'STOP'
    ) {
      const finishMsg =
        candidate.finishMessage ||
        `Model generation stopped with reason: ${finishReason}`;
      yield {
        content: {
          role: 'model',
          parts: [
            { text: `[Generation stopped: ${finishReason}] ${finishMsg}` },
          ],
        },
        errorMessage: finishMsg,
        finishReason: finishReason as any,
      };
      return;
    }

    yield {
      content: candidateContent ?? {
        role: 'model',
        parts: [],
      },
      finishReason: finishReason as any,
    };
  }

  override async connect(_llmRequest: LlmRequest): Promise<BaseLlmConnection> {
    throw new Error('Live streaming connections are not supported in sandbox');
  }
}

// Backwards-compatible alias
export { OakModel as HostModel };
