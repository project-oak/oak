# Compliance Orchestration CLI

The **CLI Orchestrator** executes deterministic, multi-round compliance
remediation pipelines across Party A (Anonymizer) and Party B (Evaluator)
enclaves over attested Oak Proxy tunnels.

## Components

- `client.py`: Typed HTTP client interfacing with Party A and Party B over local
  Oak Proxy tunnels (`127.0.0.1:8081` and `127.0.0.1:8082`). Automatically
  parses and decodes `X-Oak-Attestation` headers to extract verified AMD SEV-SNP
  hardware claims.
- `main.py`: Command-line pipeline orchestrator managing multi-round negotiation
  cycles, timing benchmarks, Rich terminal dashboards, and audit ledger
  generation.

## Features

- **Hardware Attestation Verification**: Queries `/health` to verify and display
  hardware platform and security flags before sending sensitive data.
- **Multi-Round Negotiation**: Iteratively submits dataset to Party B, reads
  remediation feedback, applies progressive transformation ladder via Party A
  (`level_1` $\rightarrow$ `level_2` $\rightarrow$ `level_3`), and repeats until
  certified `PASS`.
- **Audit Ledger Certificate**: Supports `--certificate-output` to write a
  cryptographically verifiable JSON audit bundle containing input/output SHA-256
  hashes, TEE attestation claims, and round history.

## Usage

```bash
python cli/main.py \
  --input=sample_medical_records.csv \
  --output=_scratch/compliant_records.csv \
  --certificate-output=_scratch/audit_certificate.json \
  --k=5 \
  --epsilon=0.5
```
