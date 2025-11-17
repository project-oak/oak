# Oak Proxy clients.
output "flights_proxy_external_ip" {
  value       = module.flights_proxy.external_ip
  description = "The external IP address of the Oak Proxy client for flights VM."
}

output "hotels_proxy_external_ip" {
  value       = module.hotels_proxy.external_ip
  description = "The external IP address of the Oak Proxy client for hotels VM."
}

output "activities_proxy_external_ip" {
  value       = module.activities_proxy.external_ip
  description = "The external IP address of the Oak Proxy client for activities VM."
}

# MCP servers.
output "flights_mcp_server_external_ip" {
  value       = module.flights_mcp_server.external_ip
  description = "The external IP address of the attested MCP server VM."
}

output "hotels_mcp_server_external_ip" {
  value       = module.hotels_mcp_server.external_ip
  description = "The external IP address of the attested MCP server VM."
}

output "activities_mcp_server_external_ip" {
  value       = module.activities_mcp_server.external_ip
  description = "The external IP address of the attested MCP server VM."
}

# Oak Functions.
output "flights_oak_functions_external_ip" {
  value       = module.flights_oak_functions.external_ip
  description = "The external IP address of the Oak Functions Standalone VM."
}

output "hotels_oak_functions_external_ip" {
  value       = module.hotels_oak_functions.external_ip
  description = "The external IP address of the Oak Functions Standalone VM."
}

output "activities_oak_functions_external_ip" {
  value       = module.activities_oak_functions.external_ip
  description = "The external IP address of the Oak Functions Standalone VM."
}
