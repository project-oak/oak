resource "google_compute_instance" "oak_functions_standalone" {
  name             = var.instance_name
  machine_type     = var.machine_type
  zone             = var.zone
  min_cpu_platform = "Intel Sapphire Rapids"

  scheduling {
    automatic_restart   = false
    on_host_maintenance = "TERMINATE"
  }

  boot_disk {
    initialize_params {
      image = "projects/confidential-space-images/global/images/family/confidential-space"
    }
  }

  confidential_instance_config {
    enable_confidential_compute = true
    confidential_instance_type  = "TDX"
  }
  shielded_instance_config {
    enable_secure_boot = true
  }

  service_account {
    scopes = ["cloud-platform"]
  }

  network_interface {
    network = "default"
    access_config {
      # Ephemeral public IP.
    }
  }

  metadata = {
    tee-image-reference = var.image_digest
    # Logs from the Wasm module will not be visible in any environment.
    tee-container-log-redirect = "true"
    tee-cmd                    = "[\"--wasm-uri=${var.wasm_url}\",\"--lookup-data-uri=${var.lookup_data_url}\",\"--attestation-type=self-unidirectional\",\"--listen-address=0.0.0.0:${var.exposed_port}\"]"
  }

  tags = ["oak-functions-standalone"]

  allow_stopping_for_update = true
}
