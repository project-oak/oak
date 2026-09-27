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

  metadata = {
    # Prevent the batch evaluation container from looping endlessly after signing.
    tee-restart-policy     = "Never"
    tee-env-BENCHMARK      = var.benchmark
    tee-env-RESULTS_BUCKET = var.results_bucket_name
  }
}

resource "google_storage_bucket_iam_member" "results_writer" {
  bucket = var.results_bucket_name
  role   = "roles/storage.objectAdmin"
  member = "serviceAccount:${module.confidential_space_instance.service_account_email}"
}
