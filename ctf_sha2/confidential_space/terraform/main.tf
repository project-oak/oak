terraform {
  required_providers {
    google = {
      source  = "hashicorp/google"
      version = ">= 4.50.0"
    }
  }
}

provider "google" {
  project = var.gcp_project_id
  zone    = var.zone
}

module "confidential_space_instance" {
  source = "../../../terraform/modules/confidential_space_instance"

  gcp_project_id  = var.gcp_project_id
  zone            = var.zone
  instance_name   = var.instance_name
  machine_type    = var.machine_type
  use_debug_image = var.use_debug_image
  image_digest    = var.image_digest
}