# Party A: Privacy & Anonymization Enclave Service

The **Anonymizer Service** acts as the **Privacy Service Provider (Party A)**
deployed within a Google Cloud Confidential Space enclave (AMD SEV-SNP).

## Responsibilities

- **Direct PII Masking**: Strips direct identifiers (patient IDs, visit IDs,
  names) and replaces them with cryptographically consistent pseudonyms.
- **Date Generalization**: Generalizes high-precision temporal timestamps
  (`YYYY-MM-DD`) to years (`YYYY`).
- **Optimal $k$-Anonymity**: Executes peel-search equivalence class grouping
  across quasi-identifiers (`age`, `gender`, `zip_code`) and suppresses outliers
  ($k \ge 5$).
- **Differential Privacy**: Injects calibrated Laplace perturbation into
  sensitive numeric attributes with configurable $\epsilon$ budget.
- **Synthetic Data Generation**: Synthesizes records from empirical marginal
  distributions.

## API Endpoints

- `GET /health`: Service health check.
- `POST /anonymize`: Applies composite PII masking, $k$-anonymity transformation
  (`k`), optional Differential Privacy (`apply_dp=True`, `epsilon`), or
  delegates to synthetic generation when `intensity="level_4"`.
- `POST /differential_privacy`: Perturbs numeric attributes with Laplace noise.
- `POST /synthetic`: Generates differentially private synthetic tabular records.
