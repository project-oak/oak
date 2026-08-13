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

"""Host-side Compliance Tools for ADK Agent.

Wraps attested Confidential Space enclaves (Party A Anonymizer and Party B
Evaluator) as callable ADK tools for autonomous compliance remediation.
"""

import base64
import os
import time
from typing import Any, Dict, List, Optional
import httpx


def _resolve_data_payload(data_or_path: str) -> str:
  """Resolves a dataset parameter to raw CSV string, reading from file if it exists."""
  if os.path.exists(data_or_path):
    with open(data_or_path, "r", encoding="utf-8") as f:
      return f.read()
  try:
    decoded = base64.b64decode(data_or_path, validate=True).decode("utf-8")
    if "\n" in decoded or "," in decoded:
      return decoded
  except Exception:
    pass
  return data_or_path


def _save_data_payload(data_str: str, output_path: str) -> None:
  """Writes a raw text dataset to disk."""
  try:
    decoded = base64.b64decode(data_str, validate=True).decode("utf-8")
    if "\n" in decoded or "," in decoded:
      data_str = decoded
  except Exception:
    pass

  os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
  with open(output_path, "w", encoding="utf-8") as f:
    f.write(data_str)


class ComplianceToolbox:
  """Toolbox exposing attested enclave transformations to the ADK Agent."""

  def __init__(
      self,
      anonymizer_url: str = "http://127.0.0.1:8081",
      evaluator_url: str = "http://127.0.0.1:8082",
      timeout: float = 1200.0,
  ) -> None:
    """Initializes the compliance toolbox.

    Args:
        anonymizer_url: URL for Party A Anonymizer enclave proxy.
        evaluator_url: URL for Party B Evaluator enclave proxy.
        timeout: HTTP request timeout in seconds.
    """
    self.anonymizer_url = anonymizer_url.rstrip("/")
    self.evaluator_url = evaluator_url.rstrip("/")
    self.timeout = timeout

  def evaluate_compliance(
      self,
      dataset: str,
  ) -> Dict[str, Any]:
    """Audits dataset compliance and privacy risks via attested Party B Auditor Enclave.

    Args:
        dataset: Local file path or Base64/raw CSV string.

    Returns:
        Dictionary containing audit verdict, status ('PASS' or 'FAIL'), risk level,
        violations detected, and recommended remediation parameters.
    """
    t0 = time.time()
    print(
        f"\n[Tool: evaluate_compliance] Auditing '{dataset}' via Party B"
        " Evaluator (TEE Gemma CPU inference ~60–75s)...",
        flush=True,
    )
    data_b64 = _resolve_data_payload(dataset)
    url = f"{self.evaluator_url}/evaluate"
    payload = {"data": data_b64}
    with httpx.Client(timeout=self.timeout) as client:
      resp = client.post(url, json=payload)
      resp.raise_for_status()
      result = resp.json()
      dur = time.time() - t0
      print(
          f"[Tool: evaluate_compliance] Audit Complete ({dur:.2f}s) -> Status:"
          f" {result.get('status')}, Risk: {result.get('risk_level')}",
          flush=True,
      )
      return result

  def anonymize_dataset(
      self,
      dataset: str,
      output_file: Optional[str] = None,
      k: int = 5,
      quasi_identifiers: Optional[List[str]] = None,
      intensity: str = "level_2",
      apply_dp: bool = False,
      epsilon: float = 2.0,
  ) -> Dict[str, Any]:
    """Applies progressive k-anonymity and direct identifier suppression via Party A Privacy Enclave.

    Args:
        dataset: Local file path or Base64/raw CSV string.
        output_file: Optional local file path to save transformed dataset.
        k: Target equivalence class size.
        quasi_identifiers: List of quasi-identifier column names.
        intensity: Progressive lossy intensity level ('level_1' to 'level_4').
        apply_dp: Whether to perturb numeric columns via Laplace DP.
        epsilon: Privacy budget when DP is enabled.

    Returns:
        Dictionary containing retention ratio, suppressed rows count, utility score,
        and output file path.
    """
    t0 = time.time()
    print(
        f"\n[Tool: anonymize_dataset] Applying {intensity} (k={k},"
        f" DP={apply_dp}) via Party A Enclave...",
        flush=True,
    )
    data_b64 = _resolve_data_payload(dataset)
    url = f"{self.anonymizer_url}/anonymize"
    quasi_identifiers = quasi_identifiers or ["age", "gender", "zip_code"]
    payload = {
        "data": data_b64,
        "k": k,
        "quasi_identifiers": quasi_identifiers,
        "intensity": intensity,
        "apply_dp": apply_dp,
        "epsilon": epsilon,
    }
    with httpx.Client(timeout=self.timeout) as client:
      resp = client.post(url, json=payload)
      resp.raise_for_status()
      result = resp.json()

      if output_file and "data" in result:
        _save_data_payload(result["data"], output_file)
        result["saved_to_file"] = output_file
        result["data"] = f"<saved to {output_file}>"

      dur = time.time() - t0
      print(
          f"[Tool: anonymize_dataset] Applied k-anonymity ({dur:.2f}s) ->"
          f" Retained: {result.get('records_after')}, Suppressed:"
          f" {result.get('suppressed_count')}, Saved: {output_file}",
          flush=True,
      )
      return result

  def apply_differential_privacy(
      self,
      dataset: str,
      output_file: Optional[str] = None,
      epsilon: float = 0.5,
      columns: Optional[List[str]] = None,
  ) -> Dict[str, Any]:
    """Injects calibrated Laplace noise into numeric attributes via Party A Privacy Enclave.

    Guarantees mathematical (epsilon, 0)-differential privacy for sensitive attributes.

    Args:
        dataset: Local file path or Base64/raw CSV string.
        output_file: Optional local file path to save the transformed dataset.
        epsilon: Privacy budget parameter (lower means stronger privacy/noise).
        columns: Specific numeric columns to perturb (if None, perturbs all numeric columns).

    Returns:
        Dictionary containing perturbed columns and output file path.
    """
    print(
        "\n[Tool: apply_differential_privacy] Injecting Laplace noise"
        f" (epsilon={epsilon}) via Party A Enclave...",
        flush=True,
    )
    data_b64 = _resolve_data_payload(dataset)
    url = f"{self.anonymizer_url}/differential_privacy"
    payload = {
        "data": data_b64,
        "epsilon": epsilon,
        "columns": columns,
    }
    with httpx.Client(timeout=self.timeout) as client:
      resp = client.post(url, json=payload)
      resp.raise_for_status()
      result = resp.json()

      if output_file and "data" in result:
        _save_data_payload(result["data"], output_file)
        result["saved_to_file"] = output_file
        result["data"] = f"<saved to {output_file}>"

      print(
          "[Tool: apply_differential_privacy] Applied DP -> Perturbed Columns:"
          f" {result.get('applied_columns')}, Saved: {output_file}",
          flush=True,
      )
      return result

  def generate_synthetic_data(
      self,
      dataset: str,
      output_file: Optional[str] = None,
      num_records: int = 100,
  ) -> Dict[str, Any]:
    """Generates synthetic dataset from marginal empirical distributions via Party A Enclave.

    Args:
        dataset: Local file path or Base64/raw CSV string.
        output_file: Optional local file path to save synthetic dataset.
        num_records: Number of synthetic rows to generate.

    Returns:
        Dictionary containing synthetic generation metadata and output file path.
    """
    print(
        f"\n[Tool: generate_synthetic_data] Generating {num_records} synthetic"
        " rows via Party A Enclave...",
        flush=True,
    )
    data_b64 = _resolve_data_payload(dataset)
    url = f"{self.anonymizer_url}/synthetic"
    payload = {
        "data": data_b64,
        "num_records": num_records,
    }
    with httpx.Client(timeout=self.timeout) as client:
      resp = client.post(url, json=payload)
      resp.raise_for_status()
      result = resp.json()

      if output_file and "data" in result:
        _save_data_payload(result["data"], output_file)
        result["saved_to_file"] = output_file
        result["data"] = f"<saved to {output_file}>"

      return result

  def get_attestation_claims(
      self, service: str = "evaluator"
  ) -> Dict[str, Any]:
    """Fetches verified hardware TEE attestation claims from the enclave proxy.

    Args:
        service: 'evaluator' for Party B or 'anonymizer' for Party A.

    Returns:
        Dictionary containing decoded attestation claims and hardware metadata.
    """
    url = (
        f"{self.evaluator_url if service == 'evaluator' else self.anonymizer_url}/health"
    )
    try:
      with httpx.Client(timeout=5.0) as client:
        resp = client.get(url)
        return resp.json()
    except Exception as e:
      return {"status": "error", "detail": str(e)}
