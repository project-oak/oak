module "confidential_space_instance" {
  source = "../../../terraform/modules/confidential_space_instance"

  gcp_project_id    = var.gcp_project_id
  zone              = var.zone
  instance_name     = var.instance_name
  machine_type      = var.machine_type
  image_digest      = var.image_digest
  boot_disk_size    = 50
  use_spot_vm       = true
  accelerator_type  = "nvidia-h100-80gb"
  accelerator_count = 1
  tags              = ["attested-model"]
}
