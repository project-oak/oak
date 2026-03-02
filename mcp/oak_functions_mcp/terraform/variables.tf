variable "gcp_project_id" {
  type        = string
  description = "The GCP project ID to deploy the resources in."
  default     = "oak-functions-standalone"
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
  default     = "europe-west1-docker.pkg.dev/oak-functions-standalone/oak-functions-mcp-containers/oak-functions-mcp:latest"
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
