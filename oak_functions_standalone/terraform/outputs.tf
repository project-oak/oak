output "instance_name" {
  description = "The name of the Oak Functions VM."
  value       = google_compute_instance.oak_functions.name
}

output "internal_ip" {
  value       = google_compute_instance.oak_functions.network_interface[0].network_ip
  description = "The internal IP address of the Oak Functions VM."
}

output "external_ip" {
  value       = google_compute_instance.oak_functions.network_interface[0].access_config[0].nat_ip
  description = "The external IP address of the Oak Functions VM."
}

output "self_link" {
  description = "The self-link of the Oak Functions VM."
  value       = google_compute_instance.oak_functions.self_link
}
