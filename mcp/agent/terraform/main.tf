module "confidential_space_instance" {
  source = "../../../terraform/modules/confidential_space_instance"

  gcp_project_id = var.gcp_project_id
  zone           = var.zone
  instance_name  = var.instance_name
  machine_type   = var.machine_type
  image_digest   = var.image_digest
  tags           = ["private-agent"]

  metadata = {
    tee-env-MODEL_PROXY_URL = "ws://${var.model_server_ip}:8080"
    tee-env-MCP_PROXY_URL   = "ws://${var.mcp_server_ip}:8080"
  }
}
