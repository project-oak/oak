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

import argparse
import uvicorn
from agent import create_agent
from google.adk.a2a.utils.agent_to_a2a import to_a2a


parser = argparse.ArgumentParser()
parser.add_argument(
    "--host",
    default="127.0.0.1",
    help="The host to bind the server to.",
)
parser.add_argument(
    "--port",
    type=int,
    default=8081,
    help="The port to bind the server to.",
)
parser.add_argument(
    "--mcp-server-url",
    help="The URL of the MCP server.",
)


if __name__ == "__main__":
    args = parser.parse_args()

    agent = create_agent(args.mcp_server_url)

    # Wrap the ADK agent in a Starlette web application, automatically creating the
    # necessary A2A (Agent-to-Agent) protocol endpoints and generating an agent card
    # for discovery.
    # <https://www.starlette.io/>
    # <https://a2aprotocol.ai/>
    app = to_a2a(
        agent=agent,
        host=args.host,
        port=args.port,
    )
    uvicorn.run(app, host=args.host, port=args.port, log_level="info")
