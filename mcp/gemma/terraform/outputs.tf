output "internal_ip" {
  value       = google_compute_instance.attested_gemma.network_interface[0].network_ip
  description = "The internal IP address of the attested Gemma VM."
}