# Multi-Party Sovereign Compliance Workflow with Oak

This example demonstrates a **Multi-Party Sovereign AI Compliance Architecture**
built on **Project Oak**, **Google Cloud Confidential Space**, and the **Google
Agent Development Kit (ADK)**.

It illustrates how an organization can orchestrate multi-round data
anonymization ($k$-anonymity and Differential Privacy) and independent
compliance audits across isolated, mutually-untrusted parties without exposing
raw datasets to unauthorized operators.

---

## 1. Multi-Party Architecture & Trust Topology

```text
                  ┌──────────────────────────────────────────────┐
                  │ Client / Host Boundary                       │
                  │                                              │
                  │  CLI Flow (`cli/`) or ADK Agent (`agent/`)   │
                  │   ├── Tool: `anonymize_dataset(...)`         │
                  │   └── Tool: `evaluate_compliance(...)`       │
                  │                                              │
                  │  Discovers attested status & container image │
                  │  digests purely via `X-Oak-Attestation`      │
                  └───────────────┬──────────────────────────────┘
                                  │
                 Local `oak_proxy_client` Tunnels
                 (Verifies Remote Attestation & Decrypts)
                                  │
         ┌────────────────────────┴────────────────────────┐
         │                                                 │
         ▼                                                 ▼
┌────────────────────────────────┐   ┌────────────────────────────────┐
│ Party A: Privacy Enclave       │   │ Party B: Policy Auditor        │
│ (Google Confidential Space)    │   │ (Google Confidential Space)    │
│                                │   │                                │
│ `anonymizer/` (FastAPI)        │   │ `evaluator/` (FastAPI)         │
│  - POST /anonymize (levels 1-4)│   │  - POST /evaluate (Auditor)    │
│  - POST /synthetic (Marginal)  │   │  - TEE Gemma LLM (CPU)         │
│  - `oak_proxy_server`          │   │  - `oak_proxy_server`          │
└────────────────────────────────┘   └────────────────────────────────┘

```

### Key Roles

1. **Party A (Privacy Service Provider)**: Runs the
   [anonymizer/](anonymizer/README.md) service in Confidential Space. Strips
   direct PII and supports **Progressive Anonymization Intensity Levels**
   (`level_1` minimal loss through `level_4` synthetic marginal column sampling)
   balancing utility retention vs. privacy risk.
2. **Party B (Independent Policy Auditor)**: Runs the
   [evaluator/](evaluator/README.md) service in Confidential Space. Audits data
   governance against predefined organization policy rules using a local
   TEE-resident Gemma model and guides incremental intensity escalation
   (`status="ELEVATE"` or `"PASS"`).
3. **CLI Orchestrator**: The [cli/](cli/README.md) client executes deterministic
   multi-round compliance remediation directly, stepping through intensity
   levels until certified, displaying verified hardware attestation claims, and
   writing audit ledger certificates.
4. **ADK Compliance Agent**: The [agent/](agent/README.md) autonomous agent
   (Gemini 3.6 Flash via Google ADK) coordinates privacy remediation using
   metadata-only enclave tools (preventing raw dataset exposure to Gemini API
   servers).

---

## 2. Directory Structure & Sub-Modules

| Directory / File                    | Role & Documentation                                                                                  |
| :---------------------------------- | :---------------------------------------------------------------------------------------------------- |
| [anonymizer/](anonymizer/README.md) | Party A Privacy Enclave service (FastAPI, $k$-anonymity, differential privacy, synthetic generation). |
| [evaluator/](evaluator/README.md)   | Party B Regulatory Auditor service (FastAPI, TEE Gemma LLM).                                          |
| [cli/](cli/README.md)               | Deterministic multi-round CLI orchestrator, hardware attestation table, and JSON audit certificates.  |
| [agent/](agent/README.md)           | Autonomous ADK compliance agent, path-based enclave tool wrappers, and A2A service.                   |
| [terraform/](terraform/README.md)   | Google Cloud Confidential Space deployment definitions (AMD SEV-SNP VMs).                             |
| `sample_medical_records.csv`        | Sample clinical dataset for compliance evaluation and testing.                                        |

---

## 3. Deploying to Google Cloud Confidential Space

### Step 1: Publish Container Images to Artifact Registry

All build and deployment commands should be executed from the example directory
(`oak_gcp/examples/compliance`):

```bash
cd oak_gcp/examples/compliance
export GCP_PROJECT="your-gcp-project"
export REPO_NAME="compliance-enclaves"

# Build and publish Party A
(cd anonymizer && ./publish_docker.sh "${GCP_PROJECT}" "${REPO_NAME}")

# Build and publish Party B
(cd evaluator && ./publish_docker.sh "${GCP_PROJECT}" "${REPO_NAME}")
```

### Step 2: Deploy Infrastructure via Terraform

```bash
(cd terraform && terraform init && terraform apply \
  -var="gcp_project_id=${GCP_PROJECT}" \
  -var="anonymizer_image=europe-west1-docker.pkg.dev/${GCP_PROJECT}/${REPO_NAME}/compliance-anonymizer:latest" \
  -var="evaluator_image=europe-west1-docker.pkg.dev/${GCP_PROJECT}/${REPO_NAME}/compliance-evaluator:latest")
```

Note the output public IPs: `anonymizer_public_ip` and `evaluator_public_ip`.

### Step 3: Launch Local Oak Proxy Client Tunnels

From the repository root (where `root_certificate_pem_path` resolves), start
`oak_proxy_client` instances with verified attestation and digest verification
using the checked-in proxy client configurations:

```bash
# Party A Tunnel on 127.0.0.1:8081 (Anonymizer)
./bazel-bin/oak_proxy/client/client \
  --config=oak_gcp/examples/compliance/anonymizer/proxy_client.toml \
  --server-proxy-url=ws://<ANONYMIZER_PUBLIC_IP>:8080

# Party B Tunnel on 127.0.0.1:8082 (Evaluator)
./bazel-bin/oak_proxy/client/client \
  --config=oak_gcp/examples/compliance/evaluator/proxy_client.toml \
  --server-proxy-url=ws://<EVALUATOR_PUBLIC_IP>:8080
```

### Step 4: Execute Deterministic Workflow via CLI

Execute the deterministic multi-round compliance CLI runner:

```bash
uv run python oak_gcp/examples/compliance/cli/main.py \
  --input=oak_gcp/examples/compliance/sample_medical_records.csv \
  --output=oak_gcp/examples/compliance/_scratch/certified_compliant.csv \
  --certificate-output=oak_gcp/examples/compliance/_scratch/audit_certificate.json \
  --anonymizer-url=http://127.0.0.1:8081 \
  --evaluator-url=http://127.0.0.1:8082
```

### Step 5: Execute Autonomous Compliance Agent via ADK (`adk run`)

The agent is implemented as a native **Google ADK runnable agent** in `agent/`
and can be invoked directly with the ADK CLI:

```bash
# Set your Gemini API credentials
export GEMINI_API_KEY="your-gemini-api-key"
# or export GOOGLE_API_KEY="your-gemini-api-key"

# Run single-turn autonomous audit and remediation
uv run adk run agent "Audit the dataset at sample_medical_records.csv, coordinate remediation via Party A, and save the verified compliant dataset to _scratch/agent_compliant.csv"

# Or start an interactive multi-turn ADK session
uv run adk run agent
```

---

## 4. Progressive Anonymization Escalation Ladder

The compliance pipeline steps through a 4-level progressive anonymization ladder
across rounds until Party B (`Evaluator`) certifies the dataset as compliant:

- **`level_1` (Basic Masking)**: Direct PII masking (pseudonymizing
  `patient_id`, `visit_id`, `physician`), date generalization to years, and
  $k$-anonymity with $k=2$.
- **`level_2` (Enterprise Standard)**: $k$-anonymity with $k=5$ across
  quasi-identifiers, plus Differential Privacy (Laplace noise perturbation,
  $\epsilon = 2.0$) applied to sensitive continuous clinical variables
  (`systolic_bp`, `diastolic_bp`, `heart_rate`, `glucose_mg_dl`, etc.).
- **`level_3` (High Strictness)**: $k$-anonymity with $k=10$, tighter
  Differential Privacy ($\epsilon = 0.5$), and aggressive outlier suppression.
- **`level_4` (Synthetic Fallback)**: Full differentially private synthetic
  tabular generation derived from empirical marginal distributions.

During verification, Party B (`Evaluator`) inspects dataset metadata
(`__k_level__`, `__dp_applied__`, `__intensity__`) alongside TEE LLM policy
inference to provide deterministic Level 2+ sovereign privacy verification.

---

## 5. Audit Ledger Certificate Schema

When executed with `--certificate-output`, the pipeline generates a verifiable
JSON audit bundle (`audit_certificate.json`) capturing the provenance of the
transformation:

```json
{
  "pipeline_id": "97e889fa-1234-5678-abcd-ef0123456789",
  "status": "CERTIFIED_COMPLIANT",
  "input_dataset": {
    "filename": "sample_medical_records.csv",
    "sha256_hash": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    "record_count": 51
  },
  "output_dataset": {
    "filename": "_scratch/certified_compliant.csv",
    "sha256_hash": "a1b2c3d4...",
    "record_count": 40,
    "intensity_level_applied": "level_2"
  },
  "attestation_claims": {
    "party_a_anonymizer": {
      "enclave_url": "http://127.0.0.1:8081",
      "status": "verified",
      "tee_platform": "AMD_SEV_SNP",
      "debug_allowed": false,
      "container_image_digest": "sha256:...",
      "container_image_reference": "europe-west1-docker.pkg.dev/.../compliance-anonymizer@sha256:...",
      "instance_name": "compliance-anonymizer-node",
      "handshake_handle": "...",
      "verification_time": "2026-08-18T13:16:46Z"
    },
    "party_b_evaluator": {
      "enclave_url": "http://127.0.0.1:8082",
      "status": "verified",
      "tee_platform": "AMD_SEV_SNP",
      "debug_allowed": false,
      "container_image_digest": "sha256:...",
      "container_image_reference": "europe-west1-docker.pkg.dev/.../compliance-evaluator@sha256:...",
      "instance_name": "compliance-evaluator-node",
      "handshake_handle": "...",
      "verification_time": "2026-08-18T13:16:46Z"
    }
  },
  "rounds_log": [
    {
      "round": 1,
      "audit_duration_sec": 51.45,
      "compliant": false,
      "risk_level": "HIGH",
      "remediation_strategy_applied": "level_1"
    },
    {
      "round": 2,
      "audit_duration_sec": 64.9,
      "compliant": false,
      "risk_level": "MEDIUM",
      "remediation_strategy_applied": "level_2"
    },
    {
      "round": 3,
      "audit_duration_sec": 116.25,
      "compliant": true,
      "risk_level": "LOW",
      "remediation_strategy_applied": null
    }
  ],
  "certified_at": "2026-08-18T13:28:15Z"
}
```
