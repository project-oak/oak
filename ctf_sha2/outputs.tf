output "instance_name" {
  description = "The name of the created GCE instance."
  value       = google_compute_instance.ctf_sha2_instance.name
}

output "instance_network_ip" {
  description = "The internal IP address of the GCE instance."
  value       = google_compute_instance.ctf_sha2_instance.network_interface[0].network_ip
}

output "instance_self_link" {
  description = "The self-link of the GCE instance."
  value       = google_compute_instance.ctf_sha2_instance.self_link
}
