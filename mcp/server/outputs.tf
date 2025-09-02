output "instance_name" {
  description = "The name of the created GCE instance."
  value       = google_compute_instance.attested_mcp_server.name
}

output "instance_network_ip" {
  description = "The internal IP address of the GCE instance."
  value       = google_compute_instance.attested_mcp_server.network_interface[0].network_ip
}

output "instance_external_ip" {
  description = "The external IP address of the GCE instance."
  value       = google_compute_instance.attested_mcp_server.network_interface[0].access_config[0].nat_ip
}

output "instance_self_link" {
  description = "The self-link of the GCE instance."
  value       = google_compute_instance.attested_mcp_server.self_link
}
