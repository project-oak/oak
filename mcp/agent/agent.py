#
# Copyright 2025 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the 'License');
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an 'AS IS' BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

from typing import Optional

from google.adk.agents import Agent
from google.adk.models.lite_llm import LiteLlm
from google.adk.tools.mcp_tool.mcp_toolset import (
    MCPToolset,
    StreamableHTTPConnectionParams,
)


def create_agent(mcp_server_url: Optional[str] = None) -> Agent:
    """Creates an agent with a configurable MCP server URL.

    Args:
        mcp_server_url: The URL of the MCP server. If None or empty, the agent
          will be created without MCP tools.
    """
    tools = []
    if mcp_server_url:
        tools = [
            MCPToolset(
                connection_params=StreamableHTTPConnectionParams(
                    url=mcp_server_url,
                    timeout=30.0,
                ),
            )
        ]
    return Agent(
        name="weather_agent",
        model=LiteLlm(model="ollama/gemma3:4b", timeout=30.0),
        description=(
            "Agent to answer questions about the weather at the current user"
            " location."
        ),
        instruction=(
            "You are a helpful agent who can provide current user location and"
            " also tell weather at this location."
        ),
        tools=tools,
    )


root_agent = create_agent()
