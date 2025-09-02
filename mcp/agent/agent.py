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

from google.adk.agents import Agent
from google.adk.models.lite_llm import LiteLlm
from google.adk.tools.mcp_tool.mcp_toolset import MCPToolset, StreamableHTTPConnectionParams


MCP_SERVER_URL = 'http://localhost:8080/mcp'

def get_user_location() -> dict:
    '''Retrieves the current user's location.

    Returns:
        dict: status and a dictionary with coordinates (latitude and longitude) or error message.
    '''
    return {
        'status': 'success',
        'coordinates': {
            'latitude': 45.51,
            'longitude': -122.68,
        },
    }

root_agent = Agent(
    name='weather_agent',
    model=LiteLlm(model="ollama/gemma:2b"),
    description=(
        'Agent to answer questions about the weather at the current user location.'
    ),
    instruction=(
        'You are a helpful agent who can provide current user location and also tell weather at this location.'
    ),
    tools=[
        MCPToolset(
            connection_params=StreamableHTTPConnectionParams(
                url=MCP_SERVER_URL,
                timeout=30.0,
            ),
        )],
)
