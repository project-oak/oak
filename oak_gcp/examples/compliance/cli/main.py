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

"""Example Command-Line Orchestrator for Multi-Party Sovereign Compliance.

Executes a deterministic multi-round compliance remediation flow by invoking
Party A (Anonymizer) and Party B (Evaluator) enclaves over attested Oak tunnels.
"""

import argparse
import base64
import datetime
import hashlib
import json
import os
import sys
import time
import uuid
from typing import Dict, List, Optional

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from client import ComplianceEnclaveClient
import httpx
from rich.console import Console
from rich.panel import Panel
from rich.table import Table

console = Console()


def _ensure_text(data_b64_or_raw: str) -> str:
  """Decodes Base64 to text string if necessary."""
  try:
    decoded = base64.b64decode(data_b64_or_raw.encode()).decode("utf-8")
    if "\n" in decoded or "," in decoded:
      return decoded
  except Exception:
    pass
  return data_b64_or_raw


def display_attestation_claims(client: ComplianceEnclaveClient) -> bool:
  """Fetches and displays verified hardware attestation claims from enclave proxies.

  Returns:
      bool: True if all enclave nodes are verified with AMD SEV-SNP/Confidential Space.
  """
  eval_att = client.get_attestation_claims("evaluator")
  anon_att = client.get_attestation_claims("anonymizer")

  att_table = Table(
      title="🔐 Hardware Attestation & TEE Claims (Oak Proxy L7 Inspection)"
  )
  att_table.add_column("Enclave Node", style="bold cyan")
  att_table.add_column("Status", justify="center")
  att_table.add_column("TEE Platform", style="magenta")
  att_table.add_column("Debug Allowed", justify="center")
  att_table.add_column("Handshake Handle", style="dim")
  att_table.add_column("Verification Time", style="green")

  all_verified = True
  for name, claims in [
      ("Party B (Evaluator)", eval_att),
      ("Party A (Anonymizer)", anon_att),
  ]:
    if claims and claims.get("status") == "verified":
      status_text = "[bold green]✔ VERIFIED[/bold green]"
      root = claims.get("root_layer", {})
      platform = root.get("platform") or "AMD_SEV_SNP (Confidential Space)"
      allow_debug = (
          "[green]False (Enforced)[/green]"
          if not root.get("allow_debug")
          else "[red]True[/red]"
      )
      handle = (
          claims.get("handshake_handle", "N/A")[:16] + "..."
          if claims.get("handshake_handle")
          else "N/A"
      )
      vtime = claims.get("verification_time", "N/A")
    else:
      status_text = "[bold yellow]⚠ UNVERIFIED / TCP[/bold yellow]"
      platform = "Direct / L4"
      allow_debug = "N/A"
      handle = "N/A"
      vtime = "N/A"
      all_verified = False
    att_table.add_row(name, status_text, platform, allow_debug, handle, vtime)

  console.print(att_table)
  return all_verified


def run_compliance_pipeline(
    input_file: str,
    output_file: str,
    client: ComplianceEnclaveClient,
    k: int,
    epsilon: float,
    max_rounds: int = 3,
    show_attestation: bool = True,
    certificate_output: Optional[str] = None,
    quasi_identifiers: Optional[List[str]] = None,
) -> None:
  """Executes automated multi-round compliance remediation pipeline across enclaves."""
  pipeline_start = time.perf_counter()

  with open(input_file, "r", encoding="utf-8") as f:
    raw_csv = f.read()

  # Detect active quasi-identifiers from header if not explicitly provided
  active_quasis = quasi_identifiers
  if not active_quasis:
    try:
      header_line = raw_csv.strip().splitlines()[0]
      cols = [c.strip() for c in header_line.split(",")]
      candidates = [
          "visit_date",
          "primary_condition",
          "age",
          "gender",
          "zip_code",
      ]
      active_quasis = [c for c in candidates if c in cols]
    except Exception:
      active_quasis = None

  input_hash = hashlib.sha256(raw_csv.encode()).hexdigest()
  console.print(
      Panel.fit(
          "[bold cyan]Initiating Multi-Party Sovereign Compliance"
          f" Pipeline[/bold cyan]\nInput File: [yellow]{input_file}[/yellow]"
          f" (SHA256: {input_hash[:16]}...)\nOutput Destination:"
          f" [yellow]{output_file}[/yellow]\nDefault Policy Bounds:"
          f" [bold]k={k}, epsilon={epsilon}[/bold]\nMax Remediation Rounds:"
          f" [bold]{max_rounds}[/bold]",
          title="🛡 Project Oak • GCP Confidential Space",
      )
  )

  if show_attestation:
    console.print(
        "\n[bold]Step 0: Verifying Confidential Space Hardware Attestation"
        " Claims...[/bold]"
    )
    if not display_attestation_claims(client):
      console.print(
          "\n[bold red]Error: Hardware attestation verification failed."
          " One or more enclaves are unverified or running without an attested"
          " Oak Proxy tunnel.[/bold red]\n"
          "[yellow]Refusing to transmit dataset to unverified endpoints."
          " Pass --no-attestation to bypass attestation checks in debug/local"
          " mode.[/yellow]"
      )
      sys.exit(1)

  current_data = raw_csv
  final_verdict = None
  rounds_log = []
  round_timings = {}
  applied_strategies = set()

  for round_num in range(1, max_rounds + 1):
    console.print(
        f"\n{'━'*30} [bold cyan]ROUND {round_num}[/bold cyan] {'━'*30}"
    )

    # Phase 1: Evaluation by Party B Enclave (Auditor)
    console.print(
        f"\n[bold yellow]── Round {round_num} • Phase 1: Independent Audit"
        " (Party B Enclave) ──[/bold yellow]"
    )
    t0 = time.perf_counter()
    eval_resp = client.evaluate(current_data)
    eval_duration = time.perf_counter() - t0
    round_timings[f"Round {round_num} • Phase 1 (Auditor Evaluation)"] = (
        eval_duration
    )

    final_verdict = eval_resp
    status = eval_resp.get("status", "FAIL")
    risk = eval_resp.get("risk_level", "UNKNOWN")
    reasoning = eval_resp.get("reasoning", "")
    violations = eval_resp.get("violations", [])

    table = Table(
        title=(
            f"Party B Compliance Verdict (Round {round_num} in"
            f" {eval_duration:.2f}s)"
        )
    )
    table.add_column("Property", style="cyan")
    table.add_column("Value", style="bold")

    status_colored = (
        f"[green]{status}[/green]"
        if status == "PASS"
        else (
            f"[yellow]{status}[/yellow]"
            if status == "ELEVATE"
            else f"[red]{status}[/red]"
        )
    )
    table.add_row("Status", status_colored)
    table.add_row("Risk Level", risk)
    table.add_row("Violations", str(len(violations)))
    table.add_row(
        "Reasoning",
        reasoning[:200] + "..." if len(reasoning) > 200 else reasoning,
    )
    console.print(table)

    round_record = {
        "round": round_num,
        "evaluator_verdict": eval_resp,
        "phase_1_duration_seconds": round(eval_duration, 2),
        "remediation_strategy_applied": None,
    }
    rounds_log.append(round_record)

    if eval_resp.get("compliant") and status == "PASS":
      console.print(
          "\n[bold green]✔ Dataset successfully certified compliant in Round"
          f" {round_num}![/bold green]"
      )
      break

    if round_num == max_rounds:
      console.print(
          f"\n[yellow]⚠ Reached maximum round limit ({max_rounds}). Concluding"
          " pipeline.[/yellow]"
      )
      break

    # Phase 2: Targeted Remediation by Party A Enclave (Progressive Escalation from fresh raw_csv)
    console.print(
        f"\n[bold yellow]── Round {round_num} • Phase 2: Progressive"
        " Remediation (Party A Enclave) ──[/bold yellow]"
    )
    rec = eval_resp.get("recommendation") or {}
    rec_params = rec.get("params", {}) if isinstance(rec, dict) else {}

    intensities = ["level_1", "level_2", "level_3", "level_4"]
    target_intensity = rec_params.get(
        "intensity", intensities[min(round_num - 1, len(intensities) - 1)]
    )

    t0 = time.perf_counter()
    if target_intensity == "level_4":
      synth_resp = client.generate_synthetic(raw_csv)
      rem_duration = time.perf_counter() - t0
      round_timings[
          f"Round {round_num} • Phase 2 (level_4 • Synthetic Fallback)"
      ] = rem_duration
      applied_strategies.add("synthetic")
      console.print(
          f"[green]Synthetic generation applied in {rem_duration:.2f}s.[/green]"
      )
      current_data = synth_resp["data"]
      strategy_to_apply = "level_4 (synthetic)"
    else:
      level_k = rec_params.get(
          "k",
          2
          if target_intensity == "level_1"
          else (k if target_intensity == "level_2" else 10),
      )
      level_dp = rec_params.get(
          "apply_dp", target_intensity in ["level_2", "level_3"]
      )
      level_eps = rec_params.get(
          "epsilon", epsilon if target_intensity == "level_2" else 0.5
      )

      anon_resp = client.anonymize(
          raw_csv,
          k=level_k,
          quasi_identifiers=active_quasis,
          intensity=target_intensity,
          apply_dp=level_dp,
          epsilon=level_eps,
      )
      rem_duration = time.perf_counter() - t0
      round_timings[
          f"Round {round_num} • Phase 2 ({target_intensity} • k={level_k},"
          f" DP={level_dp})"
      ] = rem_duration
      applied_strategies.add(target_intensity)
      score = anon_resp.get("utility_retention_score", 0.85)
      console.print(
          f"[green]{target_intensity} (k={level_k}, DP={level_dp}) applied in"
          f" {rem_duration:.2f}s: {anon_resp.get('records_after')} rows"
          f" retained (Utility Score: {score})[/green]"
      )
      current_data = anon_resp["data"]
      strategy_to_apply = target_intensity

    rounds_log[-1]["remediation_strategy_applied"] = strategy_to_apply

  total_time = time.perf_counter() - pipeline_start

  # Determine compliance and attestation status
  attestation_claims: Dict[str, Any] = {}
  if show_attestation:
    try:
      # Use single health check per enclave (NIT-02)
      anon_claims = client.get_attestation_claims("anonymizer")
      eval_claims = client.get_attestation_claims("evaluator")

      attestation_claims = {
          "party_a_anonymizer": (
              {
                  "enclave_url": client.anonymizer_url,
                  "oak_attestation": anon_claims,
              }
              if anon_claims
              else {
                  "enclave_url": client.anonymizer_url,
                  "status": (
                      "UNVERIFIED (Direct Local TCP / No Attestation Tunnel)"
                  ),
              }
          ),
          "party_b_evaluator": (
              {
                  "enclave_url": client.evaluator_url,
                  "oak_attestation": eval_claims,
              }
              if eval_claims
              else {
                  "enclave_url": client.evaluator_url,
                  "status": (
                      "UNVERIFIED (Direct Local TCP / No Attestation Tunnel)"
                  ),
              }
          ),
      }
    except Exception as e:
      console.print(
          "[yellow]Warning: Could not fetch attestation claims for"
          f" certificate: {e}[/yellow]"
      )

  anon_ok = bool(
      attestation_claims.get("party_a_anonymizer", {})
      .get("oak_attestation", {})
      .get("status")
      == "verified"
  )
  eval_ok = bool(
      attestation_claims.get("party_b_evaluator", {})
      .get("oak_attestation", {})
      .get("status")
      == "verified"
  )
  is_attested = anon_ok and eval_ok and show_attestation
  is_compliant = bool(final_verdict and final_verdict.get("compliant"))

  if not is_compliant:
    cert_status = "REJECTED"
  elif is_attested:
    cert_status = "APPROVED"
  else:
    cert_status = "UNVERIFIED"

  # Write dataset output with status-aware messaging (MED-03)
  output_text = _ensure_text(current_data)
  os.makedirs(os.path.dirname(output_file) or ".", exist_ok=True)
  with open(output_file, "w", encoding="utf-8") as f:
    f.write(output_text)

  if cert_status == "APPROVED":
    console.print(
        f"\n[bold green]Certified dataset written to: {output_file}[/bold"
        " green]"
    )
  elif cert_status == "UNVERIFIED":
    console.print(
        f"\n[bold yellow]Dataset written to {output_file} (Status: UNVERIFIED /"
        " Attestation Bypassed)[/bold yellow]"
    )
  else:
    console.print(
        f"\n[bold red]Dataset written to {output_file} (Status: REJECTED /"
        " Compliance Failed)[/bold red]"
    )

  if certificate_output:
    with open(output_file, "r", encoding="utf-8") as f:
      output_csv = f.read()
    output_hash = hashlib.sha256(output_csv.encode()).hexdigest()

    cert = {
        "audit_id": f"AUDIT-{uuid.uuid4().hex[:8].upper()}",
        "timestamp": (
            datetime.datetime.now(datetime.UTC)
            .isoformat()
            .replace("+00:00", "Z")
        ),
        "input_hash": input_hash,
        "output_hash": output_hash,
        "attestation_claims": attestation_claims,
        "rounds_log": rounds_log,
        "status": cert_status,
    }
    with open(certificate_output, "w", encoding="utf-8") as f:
      json.dump(cert, f, indent=2)
    console.print(
        "[bold green]Audit ledger certificate written to:"
        f" {certificate_output} (status: {cert_status})[/bold green]"
    )

  # Pipeline Performance Summary
  summary_table = Table(title="Pipeline Timing Summary (Rounds & Phases)")
  summary_table.add_column("Round & Phase", style="bold")
  summary_table.add_column("Enclave Target", style="cyan")
  summary_table.add_column("Duration", justify="right", style="green")

  for stage_name, duration in round_timings.items():
    target = (
        "Party B (Evaluator LLM)"
        if "Phase 1" in stage_name
        else "Party A (Anonymizer)"
    )
    summary_table.add_row(stage_name, target, f"{duration:.2f}s")

  summary_table.add_section()
  summary_table.add_row(
      "[bold]Total Pipeline Runtime[/bold]",
      "[bold]All Enclaves[/bold]",
      f"[bold]{total_time:.2f}s[/bold]",
  )
  console.print(summary_table)


def main() -> None:
  parser = argparse.ArgumentParser(
      description="Sovereign Compliance Workflow CLI Example"
  )
  parser.add_argument(
      "--input", default="sample_medical_records.csv", help="Input CSV dataset"
  )
  parser.add_argument(
      "--output",
      default="_scratch/compliant_records.csv",
      help="Output CSV dataset",
  )
  parser.add_argument("--k", type=int, default=5, help="k-anonymity threshold")
  parser.add_argument(
      "--epsilon", type=float, default=0.5, help="Differential privacy budget"
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
      "--quasi-identifiers",
      nargs="*",
      default=None,
      help=(
          "Optional list of quasi-identifier column names (e.g."
          " --quasi-identifiers visit_date primary_condition)"
      ),
  )
  parser.add_argument(
      "--max-rounds",
      type=int,
      default=3,
      help="Maximum negotiation and remediation rounds",
  )
  parser.add_argument(
      "--no-attestation",
      action="store_true",
      help=(
          "Bypass hardware attestation verification (records UNVERIFIED in"
          " certificate)"
      ),
  )
  parser.add_argument(
      "--certificate-output",
      default=None,
      help="Optional path to output the JSON audit ledger certificate",
  )

  args = parser.parse_args()

  client = ComplianceEnclaveClient(
      anonymizer_url=args.anonymizer_url,
      evaluator_url=args.evaluator_url,
  )

  if not os.path.exists(args.input):
    console.print(f"[red]Error: Input dataset {args.input} not found.[/red]")
    sys.exit(1)

  parsed_quasi = None
  if args.quasi_identifiers:
    parsed_quasi = [
        c.strip()
        for q in args.quasi_identifiers
        for c in q.split(",")
        if c.strip()
    ]

  run_compliance_pipeline(
      input_file=args.input,
      output_file=args.output,
      client=client,
      k=args.k,
      epsilon=args.epsilon,
      max_rounds=args.max_rounds,
      show_attestation=not args.no_attestation,
      certificate_output=args.certificate_output,
      quasi_identifiers=parsed_quasi,
  )


if __name__ == "__main__":
  main()
