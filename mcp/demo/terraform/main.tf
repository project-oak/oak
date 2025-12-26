provider "google" {
  project = var.gcp_project_id
  zone    = var.zone
}

resource "google_compute_firewall" "trusted_mcp_firewall" {
  name    = "allow-private-agent-infra"
  network = "default"

  allow {
    protocol = "tcp"
    ports    = [var.exposed_port]
  }

  target_tags   = ["attested-mcp-server", "oak-functions", "oak-proxy-client"]
  source_ranges = ["0.0.0.0/0"]
}

# Flights database.

module "flights_oak_functions" {
  source          = "../../../oak_functions_standalone/terraform"
  gcp_project_id  = var.gcp_project_id
  zone            = var.zone
  instance_name   = "flights-oak-functions"
  machine_type    = "c3-standard-4"
  image_digest    = var.oak_functions_image_digest
  lookup_data_url = var.flights_lookup_data
  exposed_port    = var.exposed_port
  # Oak Functions Terraform has its own firewall rule that would clash with `trusted_mcp_firewall`.
  create_firewall_rule = false
}

module "flights_mcp_server" {
  source           = "../../server/terraform"
  gcp_project_id   = var.gcp_project_id
  zone             = var.zone
  instance_name    = "flights-mcp-server"
  machine_type     = "c3-standard-4"
  image_digest     = var.flights_mcp_server_image_digest
  exposed_port     = var.exposed_port
  oak_functions_ip = module.flights_oak_functions.internal_ip
}

module "flights_proxy" {
  source              = "../../../oak_proxy/terraform"
  gcp_project_id      = var.gcp_project_id
  zone                = var.zone
  instance_name       = "flights-proxy"
  machine_type        = "c3-standard-4"
  image_digest        = var.oak_proxy_client_image_digest
  exposed_port        = var.exposed_port
  oak_proxy_server_ip = module.flights_mcp_server.internal_ip
}

# Hotels database.

module "hotels_oak_functions" {
  source          = "../../../oak_functions_standalone/terraform"
  gcp_project_id  = var.gcp_project_id
  zone            = var.zone
  instance_name   = "hotels-oak-functions"
  machine_type    = "c3-standard-4"
  image_digest    = var.oak_functions_image_digest
  lookup_data_url = var.hotels_lookup_data
  exposed_port    = var.exposed_port
  # Oak Functions Terraform has its own firewall rule that would clash with `trusted_mcp_firewall`.
  create_firewall_rule = false
}

module "hotels_mcp_server" {
  source           = "../../server/terraform"
  gcp_project_id   = var.gcp_project_id
  zone             = var.zone
  instance_name    = "hotels-mcp-server"
  machine_type     = "c3-standard-4"
  image_digest     = var.hotels_mcp_server_image_digest
  exposed_port     = var.exposed_port
  oak_functions_ip = module.hotels_oak_functions.internal_ip
}

module "hotels_proxy" {
  source              = "../../../oak_proxy/terraform"
  gcp_project_id      = var.gcp_project_id
  zone                = var.zone
  instance_name       = "hotels-proxy"
  machine_type        = "c3-standard-4"
  image_digest        = var.oak_proxy_client_image_digest
  exposed_port        = var.exposed_port
  oak_proxy_server_ip = module.hotels_mcp_server.internal_ip
}

# Activities database.

module "activities_oak_functions" {
  source          = "../../../oak_functions_standalone/terraform"
  gcp_project_id  = var.gcp_project_id
  zone            = var.zone
  instance_name   = "activities-oak-functions"
  machine_type    = "c3-standard-4"
  image_digest    = var.oak_functions_image_digest
  lookup_data_url = var.activities_lookup_data
  exposed_port    = var.exposed_port
  # Oak Functions Terraform has its own firewall rule that would clash with `trusted_mcp_firewall`.
  create_firewall_rule = false
}

module "activities_mcp_server" {
  source           = "../../server/terraform"
  gcp_project_id   = var.gcp_project_id
  zone             = var.zone
  instance_name    = "activities-mcp-server"
  machine_type     = "c3-standard-4"
  image_digest     = var.activities_mcp_server_image_digest
  exposed_port     = var.exposed_port
  oak_functions_ip = module.activities_oak_functions.internal_ip
}

module "activities_proxy" {
  source              = "../../../oak_proxy/terraform"
  gcp_project_id      = var.gcp_project_id
  zone                = var.zone
  instance_name       = "activities-proxy"
  machine_type        = "c3-standard-4"
  image_digest        = var.oak_proxy_client_image_digest
  exposed_port        = var.exposed_port
  oak_proxy_server_ip = module.activities_mcp_server.internal_ip
}