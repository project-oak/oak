# Party B: Policy Auditor & Evaluator Enclave Service

The **Evaluator Service** acts as an **Independent Policy & Data Governance
Auditor (Party B)** deployed within a Google Cloud Confidential Space enclave
(AMD SEV-SNP).

## Responsibilities

- **Attested Compliance Audits**: Performs structured compliance audits on
  incoming datasets using a local TEE-resident Gemma model (via Ollama on CPU).
- **Progressive Remediation Guidance**: Returns structured JSON verdicts (`PASS`
  / `FAIL`), risk assessments (`LOW` / `MEDIUM` / `HIGH`), detected violations,
  and recommended remediation parameters.

## API Endpoints

- `GET /health`: Health check, startup staged durations, and Oak Proxy
  attestation claim verification.
- `POST /evaluate`: Audits tabular data sample against privacy and governance
  compliance standards.

## Deterministic Policy Verification

In addition to LLM-based policy evaluation (`gemma4:e4b`), `POST /evaluate`
inspects dataset metadata indicators (`__k_level__`, `__dp_applied__`,
`__intensity__`). To protect against LLM generation anomalies or formatting
variations on tabular data, if a dataset meets sovereign Level 2+ privacy
requirements ($k \ge 5$ and Differential Privacy applied), the evaluator
verifies compliance with `PASS` status and `LOW` risk.
