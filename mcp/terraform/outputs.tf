output "agent_external_ip" {
  value       = module.agent.external_ip
  description = "The external IP address of the private agent VM."
}
