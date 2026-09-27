resource "google_service_account" "workload" {
  count = var.service_account_email == null ? 1 : 0

  project      = var.gcp_project_id
  account_id   = "${trimsuffix(substr(var.instance_name, 0, 27), "-")}-sa"
  display_name = "Confidential Space workload SA for ${var.instance_name}"
}

resource "google_project_iam_member" "workload_user" {
  count = var.service_account_email == null ? 1 : 0

  project = var.gcp_project_id
  role    = "roles/confidentialcomputing.workloadUser"
  member  = "serviceAccount:${google_service_account.workload[0].email}"
}

resource "google_project_iam_member" "log_writer" {
  count = var.service_account_email == null ? 1 : 0

  project = var.gcp_project_id
  role    = "roles/logging.logWriter"
  member  = "serviceAccount:${google_service_account.workload[0].email}"
}

resource "google_project_iam_member" "artifact_reader" {
  count = var.service_account_email == null ? 1 : 0

  project = var.gcp_project_id
  role    = "roles/artifactregistry.reader"
  member  = "serviceAccount:${google_service_account.workload[0].email}"
}

resource "google_compute_firewall" "allow_exposed_port" {
  count = var.exposed_port != null ? 1 : 0

  project = var.gcp_project_id
  name    = "allow-${var.instance_name}-oak-proxy"
  network = "default"

  allow {
    protocol = "tcp"
    ports    = [tostring(var.exposed_port)]
  }

  source_ranges = ["0.0.0.0/0"]
  target_tags   = [var.instance_name]
}

# GCP IAM bindings for a newly created service account are eventually consistent
# and take ~30 seconds to propagate to the Confidential Computing, Artifact
# Registry, and Cloud Logging APIs. Wait before booting the Confidential Space
# VM so confidential-space-launcher does not fail and terminate the VM on first
# boot.
resource "terraform_data" "iam_propagation" {
  count = var.service_account_email == null ? 1 : 0

  triggers_replace = [
    google_project_iam_member.workload_user[0].id,
    google_project_iam_member.log_writer[0].id,
    google_project_iam_member.artifact_reader[0].id,
  ]

  provisioner "local-exec" {
    command = "sleep 30"
  }
}

locals {
  service_account_email = (
    var.service_account_email != null
    ? var.service_account_email
    : google_service_account.workload[0].email
  )
}

resource "google_compute_instance" "confidential_space_instance" {
  project          = var.gcp_project_id
  name             = var.instance_name
  machine_type     = var.machine_type
  zone             = var.zone
  min_cpu_platform = "Intel Sapphire Rapids"
  tags             = distinct(concat(var.tags, var.exposed_port != null ? [var.instance_name] : []))

  # This instance will be terminated and re-created on maintenance events.
  scheduling {
    automatic_restart   = false
    on_host_maintenance = "TERMINATE"
    provisioning_model  = var.use_spot_vm ? "SPOT" : "STANDARD"
    preemptible         = var.use_spot_vm
  }

  # The boot disk is configured to use the Confidential Space image.
  boot_disk {
    initialize_params {
      image = (
        var.use_debug_image
        ? "projects/confidential-space-images/global/images/family/confidential-space-debug"
        : "projects/confidential-space-images/global/images/family/confidential-space"
      )
      size = var.boot_disk_size
    }
  }

  # Enable Confidential VM with Secure Boot.
  confidential_instance_config {
    enable_confidential_compute = true
    confidential_instance_type  = "TDX"
  }
  shielded_instance_config {
    enable_secure_boot = true
  }

  # The service account needs access to cloud-platform scopes to be able
  # to pull the container image and write logs.
  service_account {
    email  = local.service_account_email
    scopes = ["cloud-platform"]
  }

  # The network interface uses the default network.
  network_interface {
    network = "default"
    # This is needed for the VM to boot somehow.
    access_config {
      # Ephemeral public IP.
    }
  }

  dynamic "guest_accelerator" {
    for_each = var.accelerator_type != null ? [1] : []
    content {
      type  = var.accelerator_type
      count = var.accelerator_count
    }
  }

  # Metadata required by Confidential Space to launch the container.
  metadata = merge(
    {
      tee-image-reference        = var.image_digest
      tee-container-log-redirect = "true"
    },
    var.accelerator_type != null ? { tee-install-gpu-driver = "true" } : {},
    var.metadata,
  )

  # Allow Terraform to delete the instance.
  allow_stopping_for_update = true

  depends_on = [
    terraform_data.iam_propagation,
  ]
}
