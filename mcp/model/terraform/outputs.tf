output "instance_name" {
  description = "The name of the attested Model VM."
  value       = google_compute_instance.attested_model.name
}

output "internal_ip" {
  description = "The internal IP address of the attested Model VM."
  value       = google_compute_instance.attested_model.network_interface[0].network_ip
}

output "external_ip" {
  description = "The external IP address of the attested Model VM."
  value       = google_compute_instance.attested_model.network_interface[0].access_config[0].nat_ip
}

output "self_link" {
  description = "The self-link of the attested Model VM."
  value       = google_compute_instance.attested_model.self_link
}
