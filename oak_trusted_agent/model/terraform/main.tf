module "confidential_space_instance" {
  source = "../../../terraform/modules/confidential_space_instance"

  gcp_project_id    = var.gcp_project_id
  zone              = var.zone
  instance_name     = var.instance_name
  machine_type      = var.machine_type
  image_digest      = var.image_digest
  use_debug_image   = var.use_debug_image
  boot_disk_size    = var.boot_disk_size
  use_spot_vm       = var.use_spot_vm
  accelerator_type  = var.accelerator_type
  accelerator_count = var.accelerator_count
  exposed_port      = var.exposed_port

  metadata = {
    tee-restart-policy = "Always"
  }
}
