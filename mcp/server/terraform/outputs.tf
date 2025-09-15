output "internal_ip" {
  value       = google_compute_instance.attested_mcp_server.network_interface[0].network_ip
  description = "The internal IP address of the attested MCP server VM."
}