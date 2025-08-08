variable "gcp_project_id" {
  type        = string
  description = "The GCP project ID to deploy the resources in."
}

variable "zone" {
  type        = string
  description = "The GCP zone to deploy the resources in."
  default     = "us-west1-b"
}

variable "instance_name" {
  type        = string
  description = "The name of the GCE instance."
  default     = "ctf-sha2-test-2"
}

variable "machine_type" {
  type        = string
  description = "The machine type for the GCE instance."
  default     = "c3-standard-4"
}

variable "image_digest" {
  type        = string
  description = "The full digest of the container image to run, in the format 'IMAGE_URL@sha256:DIGEST'."
}
