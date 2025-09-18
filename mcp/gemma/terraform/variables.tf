variable "gcp_project_id" {
  type        = string
  description = "The GCP project ID to deploy the resources in."
  default     = "oak-examples-477357"
}

variable "zone" {
  type        = string
  description = "The GCP zone to deploy the resources in."
  default     = "us-east5-a"
}

variable "instance_name" {
  type        = string
  description = "The name of the GCE instance."
  default     = "attested-gemma"
}

variable "machine_type" {
  type        = string
  description = "The machine type for the GCE instance."
  default     = "a3-highgpu-1g"
}

variable "image_digest" {
  type        = string
  description = "The full reference of the container image to run, e.g., 'IMAGE_URL:latest' or 'IMAGE_URL@sha256:DIGEST'."
  default     = "europe-west1-docker.pkg.dev/oak-examples-477357/attested-gemma/attested-gemma:latest"
}

variable "exposed_port" {
  type        = number
  description = "Port on which to expose incoming TCP traffic in the GCP firewall."
  default     = 8080
}
