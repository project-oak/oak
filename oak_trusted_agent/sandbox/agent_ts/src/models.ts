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
 * Supports live model execution via WASI Preview 2 HTTP fetch().
 */

import {
  BaseLlm,
  BaseLlmConnection,
  LlmRequest,
  LlmResponse,
} from '@google/adk';

type Content = NonNullable<LlmResponse['content']>;
type Part = NonNullable<Content['parts']>[number];

interface GenerateContentApiResponse {
  candidates?: Array<{
    content?: Content;
  }>;
}

export interface ModelResponse {
  thought?: string;
  toolCall?: {
    name: string;
    args: Record<string, unknown>;
  };
  finalAnswer?: string;
}

export interface HistoryItem {
  role: 'user' | 'model' | 'tool';
  content: string;
}

export interface Model {
  generate(
    prompt: string,
    history: HistoryItem[],
  ): Promise<ModelResponse> | ModelResponse;
}

/**
 * Live Google ADK BaseLlm implementation targeting an attested Ollama / host
 * HTTP model endpoint over WASI Preview 2 HTTP fetch().
 *
 * NOTE: The agent inside the Wasm sandbox does not hold raw API keys or secrets.
 * Model requests are routed to the host or an attested proxy container (e.g.,
 * oak_proxy_server fronting Ollama in Confidential Space).
 */
export class OllamaWasiModel extends BaseLlm implements Model {
  private readonly endpointUrl: string;
  private readonly modelName: string;

  constructor(
    endpointUrl: string = 'http://127.0.0.1:8080',
    modelName: string = 'gemma4:e2b-it-qat',
  ) {
    super({ model: modelName });
    this.endpointUrl = endpointUrl;
    this.modelName = modelName;
  }

  public async generate(
    prompt: string,
    history: HistoryItem[],
  ): Promise<ModelResponse> {
    const url = `${this.endpointUrl}/v1beta/models/${this.modelName}:generateContent`;

    const contents = history.map((item) => ({
      role: item.role === 'model' ? 'model' : 'user',
      parts: [{ text: item.content }],
    }));
    contents.push({
      role: 'user',
      parts: [{ text: prompt }],
    });

    const response = await fetch(url, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ contents }),
    });

    if (!response.ok) {
      throw new Error(
        `Ollama API error: ${response.status} ${response.statusText}`,
      );
    }

    const data = (await response.json()) as GenerateContentApiResponse;
    const candidateParts: Part[] = data.candidates?.[0]?.content?.parts ?? [];
    const fnCallPart = candidateParts.find((p: Part) => p.functionCall);
    if (fnCallPart?.functionCall?.name) {
      return {
        toolCall: {
          name: fnCallPart.functionCall.name,
          args: (fnCallPart.functionCall.args as Record<string, unknown>) ?? {},
        },
      };
    }

    const candidateText = candidateParts.find((p: Part) => p.text)?.text ?? '';
    return {
      finalAnswer: candidateText,
    };
  }

  override async *generateContentAsync(
    llmRequest: LlmRequest,
  ): AsyncGenerator<LlmResponse, void> {
    const url = `${this.endpointUrl}/v1beta/models/${this.modelName}:generateContent`;

    const requestBody: Record<string, unknown> = {
      contents: llmRequest.contents,
    };
    if (llmRequest.config?.systemInstruction) {
      requestBody.systemInstruction = llmRequest.config.systemInstruction;
    }
    if (llmRequest.config?.tools) {
      requestBody.tools = llmRequest.config.tools;
    }

    const response = await fetch(url, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(requestBody),
    });

    if (!response.ok) {
      throw new Error(
        `Ollama API error: ${response.status} ${response.statusText}`,
      );
    }

    const data = (await response.json()) as GenerateContentApiResponse;
    const candidateContent = data.candidates?.[0]?.content;
    yield {
      content: candidateContent ?? {
        role: 'model',
        parts: [],
      },
    };
  }

  override async connect(_llmRequest: LlmRequest): Promise<BaseLlmConnection> {
    throw new Error('Live streaming connections are not supported in sandbox');
  }
}
