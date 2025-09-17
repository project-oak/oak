output "agent_external_ip" {
  value       = module.agent.external_ip
  description = "The external IP address of the private agent VM."
}

output "gemma_external_ip" {
  value       = module.gemma.external_ip
  description = "The external IP address of the attested Gemma VM."
}

output "mcp_server_external_ip" {
  value       = module.mcp_server.external_ip
  description = "The external IP address of the attested MCP server VM."
}
