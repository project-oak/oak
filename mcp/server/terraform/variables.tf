variable "gcp_project_id" {
  type        = string
  description = "The GCP project ID to deploy the resources in."
  default     = "oak-examples-477357"
}

variable "zone" {
  type        = string
  description = "The GCP zone to deploy the resources in."
  default     = "us-west1-b"
}

variable "instance_name" {
  type        = string
  description = "The name of the VM instance."
  default     = "attested-mcp-server"
}

variable "machine_type" {
  type        = string
  description = "The machine type for the VM."
  default     = "c3-standard-4"
}

variable "image_digest" {
  type        = string
  description = "The image digest for the MCP server container."
}

variable "exposed_port" {
  type        = number
  description = "Port on which to expose incoming TCP traffic in the GCP firewall."
  default     = 8080
}

variable "oak_functions_ip" {
  type        = string
  description = "The internal IP of the Oak Functions server."
  default     = ""
}
