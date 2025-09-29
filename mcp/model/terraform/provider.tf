provider "google" {
  project = var.gcp_project_id
  zone    = var.zone
}

resource "google_compute_firewall" "model_firewall" {
  name    = "allow-attested-model"
  network = "default"

  allow {
    protocol = "tcp"
    ports    = [var.exposed_port]
  }

  target_tags   = ["attested-model"]
  source_ranges = ["0.0.0.0/0"]
}
