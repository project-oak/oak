terraform {
  required_version = ">= 1.5.0"
  required_providers {
    google = {
      source  = "hashicorp/google"
      version = "~> 5.0"
    }
  }
}

provider "google" {
  project = var.gcp_project_id
  region  = var.region
  zone    = var.zone
}

# ------------------------------------------------------------------------------
# API Services Enablement
# ------------------------------------------------------------------------------

resource "google_project_service" "services" {
  for_each = toset([
    "artifactregistry.googleapis.com",
    "confidentialcomputing.googleapis.com",
    "compute.googleapis.com",
    "logging.googleapis.com",
  ])
  service            = each.key
  disable_on_destroy = false
}

locals {
  image_family = var.allow_debug ? "projects/confidential-space-images/global/images/family/confidential-space-debug" : "projects/confidential-space-images/global/images/family/confidential-space"
}

# ------------------------------------------------------------------------------
# Networking
# ------------------------------------------------------------------------------

resource "google_compute_network" "compliance_vpc" {
  name                    = "compliance-vpc"
  auto_create_subnetworks = true
  depends_on              = [google_project_service.services]
}

resource "google_compute_firewall" "allow_oak_proxy" {
  name    = "allow-compliance-oak-proxy"
  network = google_compute_network.compliance_vpc.name

  allow {
    protocol = "tcp"
    ports    = ["8080"]
  }

  source_ranges = ["0.0.0.0/0"]
  target_tags   = ["confidential-space-node"]
}

# ------------------------------------------------------------------------------
# IAM & Service Accounts
# ------------------------------------------------------------------------------

resource "google_service_account" "enclave_sa" {
  account_id   = "compliance-enclave-sa"
  display_name = "Service Account for Compliance TEE Enclaves"
  depends_on   = [google_project_service.services]
}

resource "google_project_iam_member" "enclave_ar_reader" {
  project = var.gcp_project_id
  role    = "roles/artifactregistry.reader"
  member  = "serviceAccount:${google_service_account.enclave_sa.email}"
}

resource "google_project_iam_member" "enclave_log_writer" {
  project = var.gcp_project_id
  role    = "roles/logging.logWriter"
  member  = "serviceAccount:${google_service_account.enclave_sa.email}"
}

resource "google_project_iam_member" "enclave_attestation_user" {
  project = var.gcp_project_id
  role    = "roles/confidentialcomputing.workloadUser"
  member  = "serviceAccount:${google_service_account.enclave_sa.email}"
}

# ------------------------------------------------------------------------------
# Artifact Registry Repository
# ------------------------------------------------------------------------------

resource "google_artifact_registry_repository" "compliance_repo" {
  location      = var.region
  repository_id = var.repo_name
  description   = "Docker repository for Compliance TEE enclave images"
  format        = "DOCKER"
  depends_on    = [google_project_service.services]
}

# ------------------------------------------------------------------------------
# Party A: Anonymizer Workload on Confidential Space
# ------------------------------------------------------------------------------

resource "google_compute_instance" "anonymizer_node" {
  name         = "compliance-anonymizer-node"
  machine_type = var.anonymizer_machine_type
  zone         = var.zone
  tags         = ["confidential-space-node"]

  boot_disk {
    initialize_params {
      image = local.image_family
      size  = 50
    }
  }

  network_interface {
    network = google_compute_network.compliance_vpc.name
    access_config {}
  }

  confidential_instance_config {
    enable_confidential_compute = true
  }

  shielded_instance_config {
    enable_integrity_monitoring = true
    enable_secure_boot          = true
    enable_vtpm                 = true
  }

  scheduling {
    on_host_maintenance = "TERMINATE"
  }

  service_account {
    email  = google_service_account.enclave_sa.email
    scopes = ["cloud-platform"]
  }

  metadata = {
    "tee-image-reference"        = var.anonymizer_image
    "tee-container-log-redirect" = "true"
  }

  allow_stopping_for_update = true

  depends_on = [
    google_project_service.services,
    google_project_iam_member.enclave_ar_reader,
    google_project_iam_member.enclave_log_writer,
    google_project_iam_member.enclave_attestation_user,
  ]
}

# ------------------------------------------------------------------------------
# Party B: Evaluator Workload on Confidential Space
# ------------------------------------------------------------------------------

resource "google_compute_instance" "evaluator_node" {
  name         = "compliance-evaluator-node"
  machine_type = var.evaluator_machine_type
  zone         = var.zone
  tags         = ["confidential-space-node"]

  boot_disk {
    initialize_params {
      image = local.image_family
      size  = 100
    }
  }

  network_interface {
    network = google_compute_network.compliance_vpc.name
    access_config {}
  }

  confidential_instance_config {
    enable_confidential_compute = true
  }

  shielded_instance_config {
    enable_integrity_monitoring = true
    enable_secure_boot          = true
    enable_vtpm                 = true
  }

  scheduling {
    on_host_maintenance = "TERMINATE"
  }

  service_account {
    email  = google_service_account.enclave_sa.email
    scopes = ["cloud-platform"]
  }

  metadata = {
    "tee-image-reference"        = var.evaluator_image
    "tee-container-log-redirect" = "true"
  }

  allow_stopping_for_update = true

  depends_on = [
    google_project_service.services,
    google_project_iam_member.enclave_ar_reader,
    google_project_iam_member.enclave_log_writer,
    google_project_iam_member.enclave_attestation_user,
  ]
}
