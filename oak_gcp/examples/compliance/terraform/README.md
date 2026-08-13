# Terraform Infrastructure for Confidential Space

This directory provides Terraform configurations to deploy Party A (Anonymizer)
and Party B (Evaluator) enclave instances on **Google Cloud Confidential Space**
with AMD SEV-SNP hardware isolation.

## Resources Provisioned

- Dedicated VPC and Subnet with secure ingress rules.
- Confidential VM instances configured with Confidential Space container images.
- Service account permissions and Workload Identity Pool bindings.

## Deployment Steps

1. Configure variables:

   ```bash
   cp terraform.tfvars.example terraform.tfvars
   # Edit terraform.tfvars with project_id and image URLs
   ```

2. Initialize and deploy:

   ```bash
   terraform init
   terraform apply
   ```

3. Outputs:
   - `anonymizer_public_ip`: Public IP for Party A enclave.
   - `evaluator_public_ip`: Public IP for Party B enclave.
