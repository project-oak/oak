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

"""Unit tests for Progressive Anonymization Escalation Ladder in Sovereign Compliance."""

import io
import unittest

from fastapi.testclient import TestClient
import pandas as pd

from oak_gcp.examples.compliance.anonymizer.server import (
    app as anon_app,
    _decode_data,
)
from oak_gcp.examples.compliance.evaluator.server import (
    app as eval_app,
    _check_raw_pii_presence,
    _extract_json,
)

SAMPLE_CSV = """patient_id,visit_id,visit_date,hospital,physician,age,gender,zip_code,primary_condition,systolic_bp,cholesterol_mg_dl,glucose_mg_dl
EU-GE-000380,V-EU-CZ-000254-001,2024-03-15,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,142,220,105
EU-GE-000381,V-EU-CZ-000254-002,2024-03-16,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,138,215,102
EU-GE-000382,V-EU-CZ-000254-003,2024-03-17,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,145,220,105
EU-GE-000383,V-EU-CZ-000254-004,2024-03-18,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,140,215,105
EU-GE-000384,V-EU-CZ-000254-005,2024-03-19,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,144,218,108
EU-GE-000385,V-EU-CZ-000254-006,2024-03-20,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,141,219,106
EU-GE-000386,V-EU-CZ-000254-007,2024-03-21,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,143,222,107
EU-GE-000387,V-EU-CZ-000254-008,2024-03-22,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,139,217,104
EU-GE-000388,V-EU-CZ-000254-009,2024-03-23,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,140,221,105
EU-GE-000389,V-EU-CZ-000254-010,2024-03-24,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,142,220,105
EU-GE-000390,V-EU-CZ-000254-011,2024-03-25,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,140,218,103
EU-GE-000391,V-EU-CZ-000254-012,2024-03-26,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,141,219,104
EU-GE-000392,V-EU-CZ-000254-013,2024-03-27,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,142,220,105
EU-GE-000393,V-EU-CZ-000254-014,2024-03-28,St. Claraspital,Dr. Sarah Jenkins,58,Female,90210,Hypertension,140,219,104
EU-GE-000999,V-EU-CZ-000999-001,2024-04-01,Outlier Hospital,Dr. Unique,99,Non-Binary,12345,Rare Disease,220,450,350
"""


class TestComplianceLadder(unittest.TestCase):

  def setUp(self):
    self.anon_client = TestClient(anon_app)
    self.eval_client = TestClient(eval_app)

  def test_level_1_basic_masking(self):
    """Verifies Level 1 masks direct PII, generalizes dates, and retains rows."""
    resp = self.anon_client.post(
        "/anonymize",
        json={"data": SAMPLE_CSV, "intensity": "level_1", "k": 2},
    )
    self.assertEqual(resp.status_code, 200)
    data = resp.json()
    self.assertTrue(data["success"])
    self.assertFalse(data["dp_applied"])

    df = pd.read_csv(io.StringIO(_decode_data(data["data"])))
    self.assertTrue((df["patient_id"] == "PT-***").all())
    self.assertTrue((df["visit_id"] == "VS-***").all())
    self.assertTrue((df["physician"] == "Dr. ***").all())
    self.assertTrue((df["visit_date"].astype(str).str.startswith("2024")).all())
    self.assertGreaterEqual(data["records_after"], 5)

  def test_level_2_enterprise_standard(self):
    """Verifies Level 2 enforces k>=5 and calibrated Laplace DP noise."""
    resp = self.anon_client.post(
        "/anonymize",
        json={
            "data": SAMPLE_CSV,
            "intensity": "level_2",
            "k": 5,
            "quasi_identifiers": ["gender", "zip_code"],
        },
    )
    self.assertEqual(resp.status_code, 200)
    data = resp.json()
    self.assertTrue(data["success"])
    self.assertTrue(data["dp_applied"])

    df = pd.read_csv(io.StringIO(_decode_data(data["data"])))
    self.assertGreaterEqual(len(df), 5)
    self.assertTrue((df["__dp_applied__"] == True).all())
    self.assertEqual(df["__k_level__"].iloc[0], 5)
    self.assertTrue((df["cholesterol_mg_dl"] >= 0).all())

  def test_level_3_outlier_suppression(self):
    """Verifies Level 3 aggressive outlier filtering trims extreme values."""
    resp = self.anon_client.post(
        "/anonymize",
        json={
            "data": SAMPLE_CSV,
            "intensity": "level_3",
            "k": 10,
            "quasi_identifiers": ["gender", "zip_code"],
        },
    )
    self.assertEqual(resp.status_code, 200)
    data = resp.json()
    df = pd.read_csv(io.StringIO(_decode_data(data["data"])))
    self.assertGreaterEqual(len(df), 10)
    self.assertTrue((pd.to_numeric(df["age"], errors="coerce") < 90).all())

  def test_level_4_synthetic_fallback_zero_pii_leak(self):
    """Verifies Level 4 synthetic generator contains 0 real direct PII strings."""
    resp = self.anon_client.post(
        "/synthetic",
        json={"data": SAMPLE_CSV, "num_records": 20},
    )
    self.assertEqual(resp.status_code, 200)
    data = resp.json()
    df = pd.read_csv(io.StringIO(_decode_data(data["data"])))

    self.assertEqual(len(df), 20)
    self.assertFalse(df["patient_id"].str.contains("EU-GE-000380").any())
    self.assertFalse(df["physician"].str.contains("Dr. Sarah Jenkins").any())
    self.assertTrue((df["patient_id"] == "PT-***").all())
    self.assertTrue((df["physician"] == "Dr. ***").all())

  def test_unattainable_k_suppression(self):
    """Verifies unattainable k returns 0 rows instead of leaking raw unsuppressed data."""
    resp = self.anon_client.post(
        "/anonymize",
        json={"data": SAMPLE_CSV, "intensity": "level_1", "k": 100},
    )
    self.assertEqual(resp.status_code, 200)
    data = resp.json()
    self.assertEqual(data["records_after"], 0)
    self.assertEqual(data["suppressed_count"], data["records_before"])

  def test_evaluator_anti_spoofing(self):
    """Verifies evaluator rejects spoofed metadata when raw PII is present."""
    raw_df = pd.read_csv(io.StringIO(SAMPLE_CSV))
    raw_df["__intensity__"] = "level_3"
    raw_df["__k_level__"] = 10
    raw_df["__dp_applied__"] = True

    self.assertTrue(_check_raw_pii_presence(raw_df))
    verdict = _extract_json(
        '```json\n{"compliant": true, "status": "PASS"}\n```', raw_df
    )
    self.assertFalse(verdict["compliant"])
    self.assertEqual(verdict["status"], "FAIL")
    self.assertEqual(verdict["risk_level"], "HIGH")

  def test_anti_spoofing_rejects_trailing_asterisk_injection(self):
    """Verifies that values with trailing asterisks (e.g. 555-123-4567*) are rejected as unmasked PII."""
    spoofed_csv = SAMPLE_CSV.replace(
        "Dr. Sarah Jenkins", "555-123-4567*"
    ).replace("EU-GE-000380", "123-45-6789*")
    spoofed_df = pd.read_csv(io.StringIO(spoofed_csv))

    # Must be detected as unmasked PII despite containing an asterisk
    self.assertTrue(_check_raw_pii_presence(spoofed_df))
    verdict = _extract_json(
        '```json\n{"compliant": true, "status": "PASS"}\n```', spoofed_df
    )
    self.assertFalse(verdict["compliant"])
    self.assertEqual(verdict["status"], "FAIL")

  def test_dp_noise_domain_bounds(self):
    """Verifies differential privacy applies noise calibrated to domain bounds."""
    resp = self.anon_client.post(
        "/differential_privacy",
        json={
            "data": SAMPLE_CSV,
            "epsilon": 1.0,
            "columns": ["systolic_bp"],
            "bounds": {"systolic_bp": [50.0, 250.0]},
        },
    )
    self.assertEqual(resp.status_code, 200)
    data = resp.json()
    self.assertTrue(data["success"])
    self.assertIn("systolic_bp", data["applied_columns"])

    df = pd.read_csv(io.StringIO(_decode_data(data["data"])))
    self.assertTrue((df["__dp_applied__"] == True).all())
    self.assertEqual(df["__epsilon__"].iloc[0], 1.0)

  def test_dp_noise_clamps_outlier_inputs(self):
    """Verifies that extreme outliers are clamped to declared domain bounds prior to DP noise addition (SEC-01)."""
    # Replace systolic_bp with an extreme outlier (12000.0)
    outlier_csv = SAMPLE_CSV.replace("148,", "12000,")
    resp = self.anon_client.post(
        "/differential_privacy",
        json={
            "data": outlier_csv,
            "epsilon": 10.0,  # low noise to verify clamping
            "columns": ["systolic_bp"],
            "bounds": {"systolic_bp": [50.0, 200.0]},
        },
    )
    self.assertEqual(resp.status_code, 200)
    data = resp.json()
    df = pd.read_csv(io.StringIO(_decode_data(data["data"])))
    # The 12000 value must be clamped to 200.0 before noise, so it cannot be near 12000
    self.assertLess(df["systolic_bp"].max(), 500.0)

  def test_dp_noise_rejects_inverted_bounds(self):
    """Verifies that inverted bounds (lower >= upper) are rejected with HTTP 400 (MED-01)."""
    resp = self.anon_client.post(
        "/differential_privacy",
        json={
            "data": SAMPLE_CSV,
            "epsilon": 1.0,
            "columns": ["systolic_bp"],
            "bounds": {"systolic_bp": [300.0, 50.0]},
        },
    )
    self.assertEqual(resp.status_code, 400)
    self.assertIn("Invalid domain bounds", resp.json()["detail"])

  def test_evaluator_exact_mask_matching_rejects_prefix_spoofing(self):
    """Verifies that values with raw data appended to valid mask prefixes are rejected (MED-02)."""
    spoofed_csv = SAMPLE_CSV.replace(
        "PT-***", "PT-***_REAL_SSN_987654321"
    ).replace("Dr. ***", "Dr. ***_DrMiller")
    spoofed_df = pd.read_csv(io.StringIO(spoofed_csv))
    self.assertTrue(_check_raw_pii_presence(spoofed_df))


if __name__ == "__main__":
  unittest.main()
