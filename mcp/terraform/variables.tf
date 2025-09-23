variable "gcp_project_id" {
  type        = string
  description = "The GCP project ID."
  default     = "oak-examples-477357"
}

variable "zone" {
  type        = string
  description = "The GCP zone to deploy the resources in."
  default     = "us-west1-b"
}

variable "gpu_zone" {
  type        = string
  description = "The GCP zone with GPUs to deploy the resources in."
  default     = "us-east5-a"
}

variable "exposed_port" {
  type        = number
  description = "Port on which to expose incoming TCP traffic in the GCP firewall."
  default     = 8080
}

variable "gemma_image_digest" {
  type        = string
  description = "The image digest for the Gemma container."
  default     = "europe-west1-docker.pkg.dev/oak-examples-477357/attested-gemma/attested-gemma:latest"
}

variable "mcp_server_image_digest" {
  type        = string
  description = "The image digest for the MCP server container."
  default     = "europe-west1-docker.pkg.dev/oak-examples-477357/attested-mcp-server/attested-mcp-server:latest"
}

variable "agent_image_digest" {
  type        = string
  description = "The image digest for the agent container."
  default     = "europe-west1-docker.pkg.dev/oak-examples-477357/private-agent/private-agent:latest"
}

variable "oak_functions_image_digest" {
  type        = string
  description = "The image digest for the Oak Functions Standalone container."
  default     = "europe-west1-docker.pkg.dev/oak-functions-standalone/oak-functions-standalone-containers/oak_functions_standalone:latest"
}
