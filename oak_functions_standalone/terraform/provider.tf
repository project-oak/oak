provider "google" {
  project = var.gcp_project_id
  zone    = var.zone
}

resource "google_compute_firewall" "oak_functions_standalone_firewall" {
  name    = "allow-oak-functions-standalone"
  network = "default"

  allow {
    protocol = "tcp"
    ports    = [var.exposed_port]
  }

  target_tags   = ["oak-functions-standalone"]
  source_ranges = ["0.0.0.0/0"]
}
