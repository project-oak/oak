provider "google" {
  project = var.gcp_project_id
  zone    = var.zone
}

resource "google_compute_firewall" "private_agent_firewall" {
  name    = "allow-mcp-services"
  network = "default"

  allow {
    protocol = "tcp"
    ports    = [var.exposed_port]
  }

  target_tags   = ["private-agent", "attested-gemma", "attested-mcp-server"]
  source_ranges = ["0.0.0.0/0"]
}

module "gemma" {
  source         = "../gemma/terraform"
  gcp_project_id = var.gcp_project_id
  zone           = var.zone
  instance_name  = "attested-gemma"
  machine_type   = "a3-highgpu-1g"
  image_digest   = var.gemma_image_digest
  exposed_port   = 8080
}

module "mcp_server" {
  source         = "../server/terraform"
  gcp_project_id = var.gcp_project_id
  zone           = var.zone
  instance_name  = "attested-mcp-server"
  machine_type   = "c3-standard-4"
  image_digest   = var.mcp_server_image_digest
  exposed_port   = 8080
}

module "agent" {
  source          = "../agent/terraform"
  gcp_project_id  = var.gcp_project_id
  zone            = var.zone
  instance_name   = "private-agent"
  machine_type    = "c3-standard-4"
  image_digest    = var.agent_image_digest
  exposed_port    = 8080
  gemma_server_ip = module.gemma.internal_ip
  mcp_server_ip   = module.mcp_server.internal_ip
}
