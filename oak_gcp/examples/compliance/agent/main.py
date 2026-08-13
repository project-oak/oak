#
# Copyright 2026 The Project Oak Authors
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

"""Main entry point for running the Sovereign Compliance ADK Agent.

Can be run in interactive chat mode or hosted as an Agent-to-Agent (A2A) service.
"""

import argparse
import base64
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from agent import create_compliance_agent
from rich.console import Console
from rich.panel import Panel
from tools import ComplianceToolbox

console = Console()


def _encode_file_base64(file_path: str) -> str:
  with open(file_path, "rb") as f:
    return base64.b64encode(f.read()).decode("utf-8")


def main() -> None:
  parser = argparse.ArgumentParser(
      description="Sovereign Compliance ADK Agent Runner"
  )
  parser.add_argument(
      "--anonymizer-url",
      default="http://127.0.0.1:8081",
      help="Party A Anonymizer proxy URL",
  )
  parser.add_argument(
      "--evaluator-url",
      default="http://127.0.0.1:8082",
      help="Party B Evaluator proxy URL",
  )
  parser.add_argument(
      "--model",
      default="gemini-3.5-flash",
      help="Underlying LLM model name (e.g. gemini-3.5-flash)",
  )
  parser.add_argument(
      "--dataset",
      help="Optional path to initial CSV dataset to load for the session",
  )
  parser.add_argument(
      "--serve",
      action="store_true",
      help="Serve agent over A2A Starlette service",
  )
  parser.add_argument(
      "--host",
      default="127.0.0.1",
      help="Host to bind A2A server to",
  )
  parser.add_argument(
      "--port",
      type=int,
      default=8080,
      help="Port to bind A2A server to",
  )

  args = parser.parse_args()

  toolbox = ComplianceToolbox(
      anonymizer_url=args.anonymizer_url,
      evaluator_url=args.evaluator_url,
  )
  agent = create_compliance_agent(toolbox=toolbox, model_name=args.model)

  if args.serve:
    import uvicorn
    from google.adk.a2a.utils.agent_to_a2a import to_a2a

    console.print(
        "[bold green]Serving Compliance Agent via A2A on"
        f" http://{args.host}:{args.port}[/bold green]"
    )
    app = to_a2a(agent=agent, host=args.host, port=args.port)
    uvicorn.run(app, host=args.host, port=args.port, log_level="info")
    return

  import asyncio
  from google.adk.cli.cli import run_cli

  agent_parent_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
  asyncio.run(
      run_cli(
          agent_parent_dir=agent_parent_dir,
          agent_folder_name="agent",
          save_session=False,
          default_llm_model=args.model,
      )
  )


if __name__ == "__main__":
  main()
