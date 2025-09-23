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
import asyncio
import httpx
import uuid
from google.adk.agents.remote_a2a_agent import A2AClientFactory
from a2a.client import ClientConfig
from a2a.utils.constants import AGENT_CARD_WELL_KNOWN_PATH
from a2a.types import (
    AgentCard,
    Message,
    Part,
    Role,
    Task,
    TextPart,
    TransportProtocol,
)


def _print_agent_response(response: Task | Message | None | tuple):
    """Parses and prints the final text response from the agent."""
    if response is None:
        print("Agent did not return a valid response.")
        return

    # The client may yield a tuple (Task, TaskUpdateEvent | None) for streaming.
    # We are interested in the Task object, which is the first element.
    if isinstance(response, tuple):
        response = response[0]

    final_part = None
    if isinstance(response, Task):
        if response.artifacts:
            final_part = response.artifacts[-1].parts[-1]
        elif (
            response.status
            and response.status.message
            and response.status.message.parts
        ):
            final_part = response.status.message.parts[-1]
    elif isinstance(response, Message):
        if response.parts:
            final_part = response.parts[-1]

    if final_part and hasattr(final_part, "root"):
        if isinstance(final_part.root, TextPart):
            print(f"Agent: {final_part.root.text}")
        else:
            print(f"Agent [non-text]: {final_part.root}")
    else:
        print("Agent did not return a final artifact.")
        if response:
            print("Full response:", response.model_dump_json(indent=2))


async def main():
    parser = argparse.ArgumentParser(
        description="A2A client for the cloud agent."
    )
    parser.add_argument(
        "--agent-url",
        default="http://127.0.0.1:8081/a2a/weather_agent",
        help=(
            "The URL of the agent's A2A endpoint (e.g.,"
            " http://host:port/a2a/agent_name)."
        ),
    )
    args = parser.parse_args()

    # Generate a unique context_id for this entire chat session.
    chat_session_id = str(uuid.uuid4())
    print(f"Starting new chat session: {chat_session_id}")
    print(f"Connecting to agent at: {args.agent_url}")
    print("Type 'exit' or 'quit' to end the chat.")
    print("-" * 20)

    async with httpx.AsyncClient(timeout=300.0) as httpx_client:
        try:
            # Fetch agent card.
            base_url = httpx.URL(args.agent_url)
            agent_card_url = base_url.join(AGENT_CARD_WELL_KNOWN_PATH)
            agent_card_response = await httpx_client.get(agent_card_url)
            agent_card_response.raise_for_status()
            agent_card_data = agent_card_response.json()
            agent_card = AgentCard(**agent_card_data)

            # Create agent client.
            config = ClientConfig(
                httpx_client,
                supported_transports=[
                    TransportProtocol.jsonrpc,
                ],
                use_client_preference=True,
            )
            factory = A2AClientFactory(config)
            client = factory.create(agent_card)
            print(f"Connected to agent: {agent_card.name}")

            # Start the continuous chat loop.
            print("-" * 20)
            while True:
                user_prompt = input("User: ")
                if user_prompt.lower() in ["exit", "quit"]:
                    print("Ending chat session.")
                    break

                # Create the message, making sure to reuse the context_id.
                message = Message(
                    message_id=str(uuid.uuid4()),
                    role=Role.user,
                    parts=[Part(root=TextPart(text=user_prompt))],
                    context_id=chat_session_id,  # Reuse the same ID
                )

                # Send the message and get the response.
                final_response = None
                async for event in client.send_message(message):
                    if isinstance(event, Task) and event.status:
                        print(f"Agent status: {event.status.state.value}...")
                    final_response = event

                # Print the agent's final response.
                _print_agent_response(final_response)

        except httpx.ReadTimeout as e:
            print(f"Request timed out waiting for agent response: {e}")
        except httpx.HTTPStatusError as e:
            print(
                f"HTTP error occurred while connecting to agent: {e.response.status_code} -"
                f" {e.response.text}"
            )
        except httpx.ConnectError as e:
            print(f"Connection error: Could not connect to {args.agent_url}. Is the agent running?")
        except Exception as e:
            print(f"Unexpected error occurred: {e} (type: {type(e)})")


if __name__ == "__main__":
    asyncio.run(main())
