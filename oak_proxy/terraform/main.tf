resource "google_compute_instance" "oak_proxy_client" {
  project          = var.gcp_project_id
  name             = var.instance_name
  machine_type     = var.machine_type
  zone             = var.zone
  min_cpu_platform = "Intel Sapphire Rapids"

  # This instance will be terminated and re-created on maintenance events.
  scheduling {
    automatic_restart   = false
    on_host_maintenance = "TERMINATE"
  }

  # The boot disk is configured to use the Confidential Space image.
  boot_disk {
    initialize_params {
      image = "projects/confidential-space-images/global/images/family/confidential-space"
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

  # Metadata required by Confidential Space to launch the container.
  metadata = {
    tee-image-reference        = var.image_digest
    tee-container-log-redirect = "true"
    tee-cmd                    = "[\"--config=/etc/proxy_client.toml\",\"--server-proxy-url=ws://${var.oak_proxy_server_ip}:${var.exposed_port}\"]"
  }

  # Add a tag to create corresponding firewall rules for.
  tags = ["oak-proxy-client"]

  # Allow Terraform to delete the instance.
  allow_stopping_for_update = true
}
