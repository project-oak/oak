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

variable "exposed_port" {
  type        = number
  description = "Port on which to expose incoming TCP traffic in the GCP firewall."
  default     = 8080
}

variable "oak_functions_image_digest" {
  type        = string
  description = "The image digest for the Oak Functions Standalone container."
  default     = "europe-west1-docker.pkg.dev/oak-functions-standalone/oak-functions-standalone-containers/oak_functions_standalone:latest"
}

variable "oak_proxy_client_image_digest" {
  type        = string
  description = "The image digest for the Oak Proxy client container."
  default     = "us-west1-docker.pkg.dev/oak-examples-477357/oak-proxy-client/oak-proxy-client:latest"
}

# Flights database.

variable "flights_lookup_data" {
  type        = string
  description = "Lookup data for Oak Functions Standalone containing flights."
  default     = "https://storage.googleapis.com/trusted_agent_demo/lookup_data/travel/flights.binarypb"
}

variable "flights_mcp_server_image_digest" {
  type        = string
  description = "The image digest for the MCP server container."
  default     = "us-west1-docker.pkg.dev/oak-examples-477357/attested-mcp-server/attested-mcp-server@sha256:5dd470983573af9b74508e9cb2afa304855fc5d7d03124d3bc49816c5821f1d7"
}

# Hotels database.

variable "hotels_lookup_data" {
  type        = string
  description = "Lookup data for Oak Functions Standalone containing hotels."
  default     = "https://storage.googleapis.com/trusted_agent_demo/lookup_data/travel/hotels.binarypb"
}

variable "hotels_mcp_server_image_digest" {
  type        = string
  description = "The image digest for the MCP server container."
  default     = "us-west1-docker.pkg.dev/oak-examples-477357/attested-mcp-server/attested-mcp-server@sha256:7d724abd0da1049d2121d67a4e31767354efabfc1337ab24b1fbbb2c43b5cf0b"
}

# Activities database.

variable "activities_lookup_data" {
  type        = string
  description = "Lookup data for Oak Functions Standalone containing activities."
  default     = "https://storage.googleapis.com/trusted_agent_demo/lookup_data/travel/activities.binarypb"
}

variable "activities_mcp_server_image_digest" {
  type        = string
  description = "The image digest for the MCP server container."
  default     = "us-west1-docker.pkg.dev/oak-examples-477357/attested-mcp-server/attested-mcp-server@sha256:616e7f6321ba8d8bb29735880471b1cc4262d27e73cb174e884f1e362558a112"
}
