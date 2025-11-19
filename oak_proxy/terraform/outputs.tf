output "instance_name" {
  description = "The name of the Oak Proxy client VM."
  value       = google_compute_instance.oak_proxy_client.name
}

output "internal_ip" {
  description = "The internal IP address of the Oak Proxy client VM."
  value       = google_compute_instance.oak_proxy_client.network_interface[0].network_ip
}

output "external_ip" {
  description = "The external IP address of the Oak Proxy client VM."
  value       = google_compute_instance.oak_proxy_client.network_interface[0].access_config[0].nat_ip
}

output "self_link" {
  description = "The self-link of the Oak Proxy client VM."
  value       = google_compute_instance.oak_proxy_client.self_link
}
