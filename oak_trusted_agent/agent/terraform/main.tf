module "confidential_space_instance" {
  source = "../../../terraform/modules/confidential_space_instance"

  gcp_project_id  = var.gcp_project_id
  zone            = var.zone
  instance_name   = var.instance_name
  machine_type    = var.machine_type
  image_digest    = var.image_digest
  use_debug_image = var.use_debug_image
  boot_disk_size  = var.boot_disk_size
  use_spot_vm     = var.use_spot_vm
  exposed_port    = var.exposed_port

  metadata = merge(
    {
      tee-restart-policy       = "Always"
      tee-env-WASM_URL         = var.wasm_url
      tee-env-MODEL_CONFIG_URL = var.model_config_url
      tee-env-MODEL_PROXY_URL  = "ws://${var.model_server_ip}:${var.model_server_port}"
      tee-env-MCP_PROXY_URLS   = join(",", [for ip in var.mcp_server_ips : "ws://${ip}:${var.mcp_server_port}"])
    },
    var.system_prompt_url != "" ? {
      tee-env-SYSTEM_PROMPT_URL = var.system_prompt_url
    } : {},
  )
}
