output "instance_name" {
  description = "The name of the private agent VM."
  value       = google_compute_instance.private_agent.name
}

output "internal_ip" {
  description = "The internal IP address of the private agent VM."
  value       = google_compute_instance.private_agent.network_interface[0].network_ip
}

output "external_ip" {
  description = "The external IP address of the private agent VM."
  value       = google_compute_instance.private_agent.network_interface[0].access_config[0].nat_ip
}

output "self_link" {
  description = "The self-link of the private agent VM."
  value       = google_compute_instance.private_agent.self_link
}
