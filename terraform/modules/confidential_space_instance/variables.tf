variable "gcp_project_id" {
  type        = string
  description = "The GCP project ID to deploy the resources in."
}

variable "zone" {
  type        = string
  description = "The GCP zone to deploy the resources in."
}

variable "instance_name" {
  type        = string
  description = "The name of the GCE instance."
}

variable "machine_type" {
  type        = string
  description = "The machine type for the GCE instance."
  default     = "c3-standard-4"
}

variable "use_debug_image" {
  type        = bool
  description = "Whether or not to use the Confidential Space debug image."
  default     = false
}

variable "boot_disk_size" {
  type        = number
  description = "Optional boot disk size in GB."
  default     = null
}

variable "use_spot_vm" {
  type        = bool
  description = "Whether to provision the instance as a Spot preemptible VM."
  default     = false
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

variable "service_account_email" {
  type        = string
  description = "Optional service account email to attach to the instance."
  default     = null
}

variable "tags" {
  type        = list(string)
  description = "Network tags to apply to the instance."
  default     = []
}

variable "image_digest" {
  type        = string
  description = "The full digest of the container image to run, in the format 'IMAGE_URL@sha256:DIGEST'."
}

variable "metadata" {
  type        = map(string)
  description = "Metadata to apply to the instance."
  default     = {}
}
