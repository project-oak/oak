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

"""Direct HTTP client for Party A and Party B compliance enclaves.

Provides typed interfaces to interact with the Anonymizer (Party A) and
Evaluator (Party B) services over local oak_proxy tunnels or direct endpoints.
"""

import base64
import json
from typing import Any, Dict, List, Optional
import httpx


class ComplianceEnclaveClient:
  """Direct HTTP client communicating with Party A and Party B enclaves."""

  def __init__(
      self,
      anonymizer_url: str = "http://127.0.0.1:8081",
      evaluator_url: str = "http://127.0.0.1:8082",
      timeout: float = 1200.0,
  ) -> None:
    """Initializes the enclave client.

    Args:
        anonymizer_url: URL for Party A Anonymizer enclave proxy.
        evaluator_url: URL for Party B Evaluator enclave proxy.
        timeout: HTTP request timeout in seconds.
    """
    self.anonymizer_url = anonymizer_url.rstrip("/")
    self.evaluator_url = evaluator_url.rstrip("/")
    self.timeout = timeout

  def get_raw_attestation_header(
      self, service: str = "evaluator"
  ) -> Optional[str]:
    """Fetches raw Base64 URL-safe X-Oak-Attestation header string from enclave proxy."""
    target_url = (
        self.evaluator_url if service == "evaluator" else self.anonymizer_url
    )
    try:
      with httpx.Client(timeout=10.0) as client:
        resp = client.get(f"{target_url}/health")
        return resp.headers.get("x-oak-attestation") or resp.headers.get(
            "X-Oak-Attestation"
        )
    except Exception:
      return None

  def get_raw_attestation_header_decoded(
      self, service: str = "evaluator"
  ) -> Optional[Dict[str, Any]]:
    """Fetches and decodes the exact unadulterated JSON payload from X-Oak-Attestation header."""
    header_val = self.get_raw_attestation_header(service)
    if header_val:
      try:
        padded = header_val + "=" * ((4 - len(header_val) % 4) % 4)
        decoded_json = base64.urlsafe_b64decode(padded.encode()).decode("utf-8")
        return json.loads(decoded_json)
      except Exception:
        return None
    return None

  def get_attestation_claims(
      self, service: str = "evaluator"
  ) -> Optional[Dict[str, Any]]:
    """Extracts and decodes verified hardware attestation claims from X-Oak-Attestation header.

    Args:
        service: 'evaluator' for Party B or 'anonymizer' for Party A.

    Returns:
        Dictionary containing decoded attestation claims or None.
    """
    target_url = (
        self.evaluator_url if service == "evaluator" else self.anonymizer_url
    )
    try:
      with httpx.Client(timeout=10.0) as client:
        resp = client.get(f"{target_url}/health")
        header_val = resp.headers.get("x-oak-attestation") or resp.headers.get(
            "X-Oak-Attestation"
        )
        health_data: Dict[str, Any] = {}
        try:
          health_data = resp.json()
        except Exception:
          pass

        if header_val:
          padded = header_val + "=" * ((4 - len(header_val) % 4) % 4)
          decoded_json = base64.urlsafe_b64decode(padded.encode()).decode(
              "utf-8"
          )
          claims = json.loads(decoded_json)
          if health_data.get("service"):
            claims["service"] = health_data["service"]
          if health_data.get("startup_timings"):
            claims["startup_timings"] = health_data["startup_timings"]
          return claims
    except Exception:
      return None
    return None

  def evaluate(
      self,
      data: str,
  ) -> Dict[str, Any]:
    """Audits tabular dataset via Party B Evaluator enclave."""
    payload: Dict[str, Any] = {
        "data": data,
    }

    with httpx.Client(timeout=self.timeout) as client:
      resp = client.post(f"{self.evaluator_url}/evaluate", json=payload)
      if resp.status_code != 200:
        raise RuntimeError(
            f"Evaluator returned HTTP {resp.status_code}: {resp.text}"
        )
      return resp.json()

  def anonymize(
      self,
      data: str,
      k: int = 5,
      quasi_identifiers: Optional[List[str]] = None,
      intensity: str = "level_2",
      apply_dp: bool = False,
      epsilon: float = 2.0,
  ) -> Dict[str, Any]:
    """Applies k-anonymity generalization and suppression via Party A Enclave.

    Args:
        data: Raw CSV string or tabular dataset.
        k: Minimum equivalence class size threshold.
        quasi_identifiers: Column names to treat as quasi-identifiers.
        intensity: Progressive intensity level ('level_1' to 'level_4').
        apply_dp: Whether to also apply differential privacy Laplace noise.
        epsilon: Differential privacy epsilon budget.

    Returns:
        Dictionary containing anonymized CSV data and retention metrics.
    """
    url = f"{self.anonymizer_url}/anonymize"
    payload: Dict[str, Any] = {
        "data": data,
        "k": k,
        "intensity": intensity,
        "apply_dp": apply_dp,
        "epsilon": epsilon,
    }
    if quasi_identifiers is not None:
      payload["quasi_identifiers"] = quasi_identifiers
    with httpx.Client(timeout=self.timeout) as client:
      resp = client.post(url, json=payload)
      resp.raise_for_status()
      return resp.json()

  def apply_dp(
      self,
      data: str,
      epsilon: float = 0.5,
      columns: Optional[List[str]] = None,
  ) -> Dict[str, Any]:
    """Applies Laplace differential privacy perturbation via Party A Enclave.

    Args:
        data: Raw CSV string or tabular dataset.
        epsilon: Differential privacy budget parameter.
        columns: Specific numeric columns to perturb (or all if None).

    Returns:
        Dictionary containing perturbed CSV data and applied columns.
    """
    url = f"{self.anonymizer_url}/differential_privacy"
    payload = {
        "data": data,
        "epsilon": epsilon,
        "columns": columns,
    }
    with httpx.Client(timeout=self.timeout) as client:
      resp = client.post(url, json=payload)
      resp.raise_for_status()
      return resp.json()

  def generate_synthetic(
      self,
      data: str,
      num_records: int = 100,
  ) -> Dict[str, Any]:
    """Generates synthetic dataset from marginal empirical distributions.

    Args:
        data: Raw CSV string or tabular dataset.
        num_records: Number of synthetic rows to generate.

    Returns:
        Dictionary containing synthetic CSV data.
    """
    url = f"{self.anonymizer_url}/synthetic"
    payload = {
        "data": data,
        "num_records": num_records,
    }
    with httpx.Client(timeout=self.timeout) as client:
      resp = client.post(url, json=payload)
      resp.raise_for_status()
      return resp.json()
