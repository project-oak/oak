output "external_ip" {
  value       = google_compute_instance.private_agent.network_interface[0].access_config[0].nat_ip
  description = "The external IP address of the private agent VM."
}