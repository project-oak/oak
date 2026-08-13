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

"""End-to-end integration simulation test for Sovereign Compliance Pipeline."""

import io
import json
import os
import tempfile
import unittest
from unittest.mock import MagicMock, patch

import pandas as pd

from oak_gcp.examples.compliance.cli.client import ComplianceEnclaveClient
from oak_gcp.examples.compliance.cli.main import run_compliance_pipeline

SAMPLE_CSV = """patient_id,visit_id,visit_date,hospital,physician,age,gender,zip_code,primary_condition,systolic_bp,cholesterol_mg_dl,glucose_mg_dl
EU-GE-000380,V-EU-CZ-000254-001,2024-03-15,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,142,220,105
EU-GE-000381,V-EU-CZ-000254-002,2024-03-16,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,138,215,102
EU-GE-000382,V-EU-CZ-000254-003,2024-03-17,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,145,220,105
EU-GE-000383,V-EU-CZ-000254-004,2024-03-18,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,140,215,105
EU-GE-000384,V-EU-CZ-000254-005,2024-03-19,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,144,218,108
EU-GE-000385,V-EU-CZ-000254-006,2024-03-20,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,141,219,106
"""


class TestEndToEndPipeline(unittest.TestCase):

  def test_multi_round_escalation_flow(self):
    """Simulates multi-round negotiation flow and verifies certificate generation."""
    with tempfile.TemporaryDirectory() as tmpdir:
      input_path = os.path.join(tmpdir, "input.csv")
      output_path = os.path.join(tmpdir, "output.csv")
      cert_path = os.path.join(tmpdir, "cert.json")

      with open(input_path, "w", encoding="utf-8") as f:
        f.write(SAMPLE_CSV)

      mock_client = MagicMock(spec=ComplianceEnclaveClient)
      mock_client.anonymizer_url = "http://127.0.0.1:8081"
      mock_client.evaluator_url = "http://127.0.0.1:8082"
      mock_client.get_attestation_claims.return_value = {
          "status": "verified",
          "root_layer": {"platform": "AMD_SEV_SNP", "allow_debug": False},
      }
      mock_client.get_raw_attestation_header.return_value = None
      mock_client.get_raw_attestation_header_decoded.return_value = None

      # Round 1: Evaluator returns FAIL -> Remediates to level_1
      # Round 2: Evaluator returns ELEVATE -> Remediates to level_2
      # Round 3: Evaluator returns PASS
      def mock_evaluate(data_str):
        if "__dp_applied__" in data_str and "__k_level__" in data_str:
          return {
              "compliant": True,
              "status": "PASS",
              "risk_level": "LOW",
              "reasoning": (
                  "Dataset verified compliant with Level 2+ sovereign privacy"
                  " rules."
              ),
              "violations": [],
              "recommendation": None,
          }
        elif "PT-***" in data_str:
          return {
              "compliant": False,
              "status": "ELEVATE",
              "risk_level": "MEDIUM",
              "reasoning": (
                  "Level 1 insufficient. Needs Level 2 (k=5 with DP noise)."
              ),
              "violations": ["Standard governance requires k>=5 and DP noise"],
              "recommendation": {
                  "strategy": "anonymize",
                  "params": {"intensity": "level_2", "k": 5, "epsilon": 2.0},
              },
          }
        else:
          return {
              "compliant": False,
              "status": "FAIL",
              "risk_level": "HIGH",
              "reasoning": "Raw identifiers present.",
              "violations": ["Raw PII present"],
              "recommendation": {
                  "strategy": "anonymize",
                  "params": {"intensity": "level_1", "k": 2},
              },
          }

      def mock_anonymize(
          data_str,
          k=5,
          quasi_identifiers=None,
          intensity="level_2",
          apply_dp=True,
          epsilon=2.0,
      ):
        df = pd.read_csv(io.StringIO(data_str))
        df["patient_id"] = "PT-***"
        if apply_dp:
          df["__dp_applied__"] = True
          df["__k_level__"] = k
          df["__intensity__"] = intensity
        return {
            "success": True,
            "data": df.to_csv(index=False),
            "records_before": len(df),
            "records_after": len(df),
            "suppressed_count": 0,
            "optimal_peel_level": 1,
            "intensity_applied": intensity,
            "utility_retention_score": 0.85,
            "dp_applied": apply_dp,
        }

      mock_client.evaluate.side_effect = mock_evaluate
      mock_client.anonymize.side_effect = mock_anonymize

      # 1. Attested execution: show_attestation=True -> Status APPROVED
      run_compliance_pipeline(
          input_file=input_path,
          output_file=output_path,
          client=mock_client,
          k=5,
          epsilon=2.0,
          max_rounds=3,
          show_attestation=True,
          certificate_output=cert_path,
      )

      self.assertTrue(os.path.exists(output_path))
      with open(output_path, "r", encoding="utf-8") as f:
        out_content = f.read()
      self.assertIn("PT-***", out_content)
      self.assertIn("__dp_applied__", out_content)

      self.assertTrue(os.path.exists(cert_path))
      with open(cert_path, "r", encoding="utf-8") as f:
        cert = json.load(f)
      self.assertEqual(cert["status"], "APPROVED")
      self.assertIn("audit_id", cert)
      self.assertIn("input_hash", cert)
      self.assertIn("output_hash", cert)

      # 2. Unattested bypass: show_attestation=False -> Status UNVERIFIED
      cert_unverified_path = os.path.join(tmpdir, "cert_unverified.json")
      run_compliance_pipeline(
          input_file=input_path,
          output_file=output_path,
          client=mock_client,
          k=5,
          epsilon=2.0,
          max_rounds=3,
          show_attestation=False,
          certificate_output=cert_unverified_path,
      )
      with open(cert_unverified_path, "r", encoding="utf-8") as f:
        cert_unverified = json.load(f)
      self.assertEqual(cert_unverified["status"], "UNVERIFIED")

  def test_unverified_attestation_halts_pipeline(self):
    """Verifies pipeline stops with error if enclaves are unverified and attestation is not bypassed."""
    with tempfile.TemporaryDirectory() as tmpdir:
      input_path = os.path.join(tmpdir, "input.csv")
      output_path = os.path.join(tmpdir, "output.csv")
      with open(input_path, "w", encoding="utf-8") as f:
        f.write(SAMPLE_CSV)

      mock_client = MagicMock(spec=ComplianceEnclaveClient)
      # Evaluator returns None or unverified status
      mock_client.get_attestation_claims.return_value = None

      with self.assertRaises(SystemExit):
        run_compliance_pipeline(
            input_file=input_path,
            output_file=output_path,
            client=mock_client,
            k=5,
            epsilon=2.0,
            max_rounds=3,
            show_attestation=True,
        )


if __name__ == "__main__":
  unittest.main()
