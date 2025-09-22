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
  default     = "oak-functions-standalone"
}

variable "machine_type" {
  type        = string
  description = "The machine type for the VM."
  default     = "c3-standard-4"
}

variable "image_digest" {
  type        = string
  description = "The image digest for the Oak Functions Standalone container."
  default     = "europe-west1-docker.pkg.dev/oak-functions-standalone/oak-functions-standalone-containers/oak_functions_standalone:latest"
}

variable "wasm_url" {
  type        = string
  description = "URL for the Wasm module."
  default     = "https://storage.googleapis.com/oak-functions-standalone-bucket/wasm/key_value_lookup.wasm"
}

variable "lookup_data_url" {
  type        = string
  description = "URL for the lookup data."
  default     = "https://storage.googleapis.com/oak-functions-standalone-bucket/lookup_data/fake_weather_data.binarypb"
}

variable "exposed_port" {
  type        = number
  description = "Port on which to expose incoming TCP traffic in the GCP firewall."
  default     = 8080
}
