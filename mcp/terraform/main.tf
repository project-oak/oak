provider "google" {
  project = var.gcp_project_id
  zone    = var.zone
}

resource "google_compute_firewall" "private_agent_firewall" {
  name    = "allow-private-agent-infra"
  network = "default"

  allow {
    protocol = "tcp"
    ports    = [var.exposed_port]
  }

  target_tags   = ["private-agent", "attested-model", "attested-mcp-server", "oak-functions"]
  source_ranges = ["0.0.0.0/0"]
}

module "model" {
  source         = "../model/terraform"
  gcp_project_id = var.gcp_project_id
  zone           = var.gpu_zone
  instance_name  = "attested-model"
  machine_type   = "a3-highgpu-1g"
  image_digest   = var.model_image_digest
  exposed_port   = var.exposed_port
}

module "oak_functions" {
  source         = "../../oak_functions_standalone/terraform"
  gcp_project_id = var.gcp_project_id
  zone           = var.zone
  instance_name  = "oak-functions"
  machine_type   = "c3-standard-4"
  image_digest   = var.oak_functions_image_digest
  exposed_port   = var.exposed_port
}

module "mcp_server" {
  source           = "../server/terraform"
  gcp_project_id   = var.gcp_project_id
  zone             = var.zone
  instance_name    = "attested-mcp-server"
  machine_type     = "c3-standard-4"
  image_digest     = var.mcp_server_image_digest
  exposed_port     = var.exposed_port
  oak_functions_ip = module.oak_functions.internal_ip
}

module "agent" {
  source          = "../agent/terraform"
  gcp_project_id  = var.gcp_project_id
  zone            = var.zone
  instance_name   = "private-agent"
  machine_type    = "c3-standard-4"
  image_digest    = var.agent_image_digest
  exposed_port    = var.exposed_port
  model_server_ip = module.model.internal_ip
  mcp_server_ip   = module.mcp_server.internal_ip
}
