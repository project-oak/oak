variable "gcp_project_id" {
  type        = string
  description = "The GCP project ID where Confidential Space enclaves will be deployed."
}

variable "region" {
  type        = string
  default     = "europe-west1"
  description = "GCP region for deployment."
}

variable "zone" {
  type        = string
  default     = "europe-west1-b"
  description = "GCP zone for compute instances."
}

variable "repo_name" {
  type        = string
  default     = "compliance-enclaves"
  description = "Artifact Registry Docker repository name."
}

variable "anonymizer_image" {
  type        = string
  description = "Container image URL for the Party A Anonymizer service."
}

variable "evaluator_image" {
  type        = string
  description = "Container image URL for the Party B Evaluator service."
}

variable "anonymizer_machine_type" {
  type        = string
  default     = "n2d-standard-4"
  description = "Machine type for the Anonymizer node."
}

variable "evaluator_machine_type" {
  type        = string
  default     = "n2d-standard-32"
  description = "Machine type for the Evaluator node (AMD SEV-SNP with 32 vCPUs for fast CPU LLM inference)."
}


variable "allow_debug" {
  type        = bool
  default     = false
  description = "Whether to use Confidential Space debug image family for interactive debugging."
}
