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
  default     = "oak-functions-mcp-server"
}

variable "machine_type" {
  type        = string
  description = "The machine type for the VM."
  default     = "c3-standard-4"
}

variable "image_digest" {
  type        = string
  description = "The image digest for the Oak Functions MCP server container."
  default     = "us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/mcp/server:latest"
}

variable "wasm_url" {
  type        = string
  description = "The URL for fetching the Wasm logic module."
  default     = "https://storage.googleapis.com/oak-functions-standalone-bucket/wasm/key_value_lookup_with_json.wasm"
}

variable "lookup_data_url" {
  type        = string
  description = "The URL for fetching the serialized LookupDataChunk data."
  default     = "https://storage.googleapis.com/oak-functions-standalone-bucket/lookup_data/double_lookup_data.binarypb"
}

variable "tool_config_url" {
  type        = string
  description = "The URL for fetching the ToolConfig JSON file."
  default     = "https://storage.googleapis.com/oak-functions-standalone-bucket/tool_config/key_value_lookup.json"
}

variable "use_debug_image" {
  type        = bool
  description = "Whether or not to use the Confidential Space debug image."
  default     = false
}
