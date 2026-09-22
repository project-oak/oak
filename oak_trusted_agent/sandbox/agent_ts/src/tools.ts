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
 * Adapter bridging host-provided WIT tools (oak:agent/tools@0.1.0)
 * to Google ADK's BaseTool and BaseToolset abstractions.
 */

import {
  BaseTool,
  BaseToolset,
  getLogger,
  ReadonlyContext,
  RunAsyncToolRequest,
} from '@google/adk';
import type { ToolDescription } from 'oak:agent/tools@0.1.0';

const logger = getLogger();

type FunctionDeclaration = NonNullable<ReturnType<BaseTool['_getDeclaration']>>;

/**
 * Interface representing the WIT `oak:agent/tools@0.1.0` host import module.
 * Across the WebAssembly Component Model boundary, tool schemas, arguments,
 * and results are serialized as JSON strings.
 */
export interface WitTools {
  listTools(): ToolDescription[];
  callTool(name: string, args: string): string;
}

export interface HostTool {
  name: string;
  description: string;
  inputSchema: Record<string, unknown>;
  execute(args: Record<string, unknown>): unknown;
}

/**
 * Google ADK BaseTool implementation backed by a WIT host tool import.
 */
export class WitHostTool extends BaseTool implements HostTool {
  public readonly inputSchema: Record<string, unknown>;
  private readonly callToolFn: (name: string, args: string) => string;

  constructor(
    name: string,
    description: string,
    inputSchema: Record<string, unknown>,
    callToolFn: (name: string, args: string) => string,
  ) {
    super({ name, description });
    this.inputSchema = inputSchema;
    this.callToolFn = callToolFn;
  }

  override _getDeclaration(): FunctionDeclaration {
    return {
      name: this.name,
      description: this.description,
      parametersJsonSchema: this.inputSchema,
    };
  }

  public execute(args: Record<string, unknown>): unknown {
    logger.info(`[Trusted Agent] Invoking host tool '${this.name}'`);
    const argsStr = JSON.stringify(args || {});
    const rawResult = this.callToolFn(this.name, argsStr);
    try {
      return JSON.parse(rawResult) as unknown;
    } catch {
      return rawResult;
    }
  }

  override async runAsync(request: RunAsyncToolRequest): Promise<unknown> {
    return this.execute(request.args);
  }
}

/**
 * Google ADK BaseToolset that dynamically discovers and invokes host-provided
 * tools across the WIT boundary.
 *
 * NOTE: Tool discovery is performed lazily at runtime, NOT at module load time.
 * This is essential for Wizer build-time snapshotting, which forbids calling host
 * imports during module pre-initialization.
 */
export class HostToolRegistry extends BaseToolset {
  private readonly witTools: WitTools;
  private readonly tools: Map<string, WitHostTool> = new Map();

  constructor(witTools: WitTools) {
    super([]);
    this.witTools = witTools;
    // Tool discovery is deferred until runtime to avoid executing host
    // imports during Wizer pre-initialization.
  }

  public discoverHostTools(): void {
    const rawTools: ToolDescription[] = this.witTools.listTools();
    for (const t of rawTools) {
      let schemaObj: Record<string, unknown>;
      try {
        schemaObj = JSON.parse(t.inputSchema) as Record<string, unknown>;
      } catch (e) {
        logger.error(
          `[Trusted Agent] Invalid JSON in inputSchema for tool '${t.name}': ${e}`,
        );
        throw e;
      }

      this.tools.set(
        t.name,
        new WitHostTool(t.name, t.description, schemaObj, (name, args) =>
          this.witTools.callTool(name, args),
        ),
      );
    }
  }

  public getTool(name: string): WitHostTool | undefined {
    if (!this.tools.has(name)) {
      this.discoverHostTools();
    }
    return this.tools.get(name);
  }

  public listTools(): WitHostTool[] {
    this.discoverHostTools();
    return Array.from(this.tools.values());
  }

  override async getTools(_context?: ReadonlyContext): Promise<BaseTool[]> {
    return this.listTools();
  }

  override async close(): Promise<void> {}

  public call(name: string, args: Record<string, unknown>): unknown {
    const tool = this.getTool(name);
    if (!tool) {
      throw new Error(`Tool '${name}' not found in registry`);
    }
    return tool.execute(args);
  }
}
