variable "gcp_project_id" {
  type        = string
  description = "The GCP project ID to deploy the resources in."
  default     = "oak-examples-477357"
}

variable "zone" {
  type        = string
  description = "The GCP zone to deploy the resources in."
  default     = "us-central1-a"
}

variable "instance_name" {
  type        = string
  description = "The name of the Confidential Space GCE instance."
  default     = "trusted-agent"
}

variable "machine_type" {
  type        = string
  description = "The machine type for the GCE instance."
  default     = "c3-standard-4"
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
  default     = "us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/agent:latest"
}

variable "exposed_port" {
  type        = number
  description = "TCP port exposed by oak_proxy_server for incoming Oak Session WebSocket connections."
  default     = 8080
}

variable "model_server_ip" {
  type        = string
  description = "The internal IP address of the attested Model server VM."
}

variable "model_server_port" {
  type        = number
  description = "The TCP port of the attested Model server's oak_proxy_server."
  default     = 8080
}

variable "mcp_server_ips" {
  type        = list(string)
  description = "Ordered list of internal IP addresses for attested MCP tool server VMs."
  default     = []
}

variable "mcp_server_port" {
  type        = number
  description = "The TCP port of each attested MCP server's oak_proxy_server."
  default     = 8080
}

variable "system_prompt_url" {
  type        = string
  description = "Optional URL from which the agent fetches its system prompt at startup."
  default     = ""
}
