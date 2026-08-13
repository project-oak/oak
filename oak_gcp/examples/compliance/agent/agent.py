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

"""Compliance ADK Agent Definition.

Constructs an autonomous ADK Agent powered by Gemini 3.5 Flash that coordinates
data anonymization and compliance verification across attested enclaves.
"""

import os
import sys
from typing import Optional

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from google.adk.agents import Agent

try:
  from .tools import ComplianceToolbox
except ImportError:
  from tools import ComplianceToolbox


def read_file(filepath: str) -> str:
  """Reads a file from the local filesystem."""
  with open(filepath, "r") as f:
    return f.read()


def write_file(filepath: str, content: str) -> str:
  """Writes content to a file on the local filesystem."""
  dirname = os.path.dirname(os.path.abspath(filepath))
  if dirname:
    os.makedirs(dirname, exist_ok=True)
  with open(filepath, "w") as f:
    f.write(content)
  return f"Successfully wrote to {filepath}"


AGENT_INSTRUCTION = """
You are an expert Sovereign AI Compliance Officer.
Your objective is to inspect sensitive user datasets, audit them for privacy violations,
and coordinate multi-round anonymization and differential privacy transformations
via attested Confidential Space enclaves until the dataset is certified compliant.

Execution Strategy:
1. Always start by auditing the dataset using `evaluate_compliance`.
2. If violations are detected:
   - If direct PII or ungeneralized quasi-identifiers are flagged, invoke `anonymize_dataset` with appropriate k threshold.
   - If numeric attribute inference risk is flagged, invoke `apply_differential_privacy`.
   - If requested to synthesize data from empirical marginals, invoke `generate_synthetic_data`.
3. Re-evaluate compliance on the transformed dataset using `evaluate_compliance`.
4. Conclude once `evaluate_compliance` returns status="PASS" and risk_level="LOW".
"""


def create_compliance_agent(
    toolbox: Optional[ComplianceToolbox] = None,
    model_name: str = "gemini-3.6-flash",
) -> Agent:
  """Instantiates the Sovereign Compliance ADK Agent with enclave tools."""
  if toolbox is None:
    toolbox = ComplianceToolbox()

  return Agent(
      name="sovereign_compliance_agent",
      model=model_name,
      description=(
          "Autonomous agent coordinating privacy-preserving compliance across"
          " attested TEE enclaves."
      ),
      instruction=AGENT_INSTRUCTION,
      tools=[
          toolbox.evaluate_compliance,
          toolbox.anonymize_dataset,
          toolbox.apply_differential_privacy,
          toolbox.generate_synthetic_data,
          toolbox.get_attestation_claims,
          toolbox.generate_audit_certificate,
      ],
  )


root_agent = create_compliance_agent()
