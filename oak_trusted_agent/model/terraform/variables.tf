variable "gcp_project_id" {
  type        = string
  description = "The GCP project ID to deploy the resources in."
  default     = "oak-examples-477357"
}

variable "zone" {
  type        = string
  description = "The GCP zone to deploy the resources in (use 'us-east5-a' for H100)."
  default     = "us-central1-a"
}

variable "instance_name" {
  type        = string
  description = "The name of the Confidential Space GCE instance."
  default     = "trusted-model"
}

variable "machine_type" {
  type        = string
  description = "The machine type for the GCE instance (use 'a3-highgpu-1g' for H100)."
  default     = "c3-standard-4"
}

variable "accelerator_type" {
  type        = string
  description = "Optional guest accelerator type, e.g. 'nvidia-h100-80gb'."
  default     = null
}

variable "accelerator_count" {
  type        = number
  description = "Number of guest accelerators to attach when accelerator_type is set."
  default     = 1
}

variable "boot_disk_size" {
  type        = number
  description = "Boot disk size in GB."
  default     = 50
}

variable "use_spot_vm" {
  type        = bool
  description = "Whether to provision the instance as a Spot preemptible VM."
  default     = true
}

variable "use_debug_image" {
  type        = bool
  description = "Whether to use the Confidential Space debug image."
  default     = false
}

variable "image_digest" {
  type        = string
  description = "The container image reference to run, ideally pinned by '@sha256:DIGEST'."
  default     = "us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/model/gemma4-e2b-it-qat:latest"
}

variable "exposed_port" {
  type        = number
  description = "TCP port exposed by oak_proxy_server for incoming Oak Session WebSocket connections."
  default     = 8080
}
