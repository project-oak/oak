provider "google" {
  project = var.gcp_project_id
  zone    = var.zone
}

resource "google_compute_firewall" "oak_functions_firewall" {
  count   = var.create_firewall_rule ? 1 : 0
  name    = "allow-oak-functions"
  network = "default"

  allow {
    protocol = "tcp"
    ports    = [var.exposed_port]
  }

  target_tags   = ["oak-functions"]
  source_ranges = ["0.0.0.0/0"]
}
