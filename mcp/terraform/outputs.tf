output "agent_external_ip" {
  value       = module.agent.external_ip
  description = "The external IP address of the private agent VM."
}

output "model_external_ip" {
  value       = module.model.external_ip
  description = "The external IP address of the attested Model VM."
}

output "mcp_server_external_ip" {
  value       = module.mcp_server.external_ip
  description = "The external IP address of the attested MCP server VM."
}

output "oak_functions_external_ip" {
  value       = module.oak_functions.external_ip
  description = "The external IP address of the Oak Functions Standalone VM."
}
