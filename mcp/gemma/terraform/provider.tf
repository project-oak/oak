provider "google" {
  project = var.gcp_project_id
  zone    = var.zone
}

resource "google_compute_firewall" "gemma_firewall" {
  name    = "allow-attested-gemma"
  network = "default"

  allow {
    protocol = "tcp"
    ports    = [var.exposed_port]
  }

  target_tags   = ["attested-gemma"]
  source_ranges = ["0.0.0.0/0"]
}
