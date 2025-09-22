output "instance_name" {
  description = "The name of the Oak Functions Standalone VM."
  value       = google_compute_instance.oak_functions_standalone.name
}

output "internal_ip" {
  value       = google_compute_instance.oak_functions_standalone.network_interface[0].network_ip
  description = "The internal IP address of the Oak Functions Standalone VM."
}

output "external_ip" {
  value       = google_compute_instance.oak_functions_standalone.network_interface[0].access_config[0].nat_ip
  description = "The external IP address of the Oak Functions Standalone VM."
}

output "self_link" {
  description = "The self-link of the Oak Functions Standalone VM."
  value       = google_compute_instance.oak_functions_standalone.self_link
}
