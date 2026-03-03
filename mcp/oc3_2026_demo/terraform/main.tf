module "confidential_space_instance" {
  source = "../../../terraform/modules/confidential_space_instance"

  gcp_project_id  = var.gcp_project_id
  zone            = var.zone
  instance_name   = var.instance_name
  machine_type    = var.machine_type
  image_digest    = var.image_digest
  use_debug_image = var.use_debug_image

  metadata = {
    tee-env-WASM_URL        = var.wasm_url
    tee-env-LOOKUP_DATA_URL = var.lookup_data_url
    tee-env-TOOL_CONFIG_URL = var.tool_config_url
  }
}
