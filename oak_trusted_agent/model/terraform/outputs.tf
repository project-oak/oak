output "instance_name" {
  description = "The name of the Confidential Space VM."
  value       = module.confidential_space_instance.instance_name
}

output "internal_ip" {
  description = "The internal IP address of the Confidential Space VM."
  value       = module.confidential_space_instance.instance_network_ip
}

output "external_ip" {
  description = "The external IP address of the Confidential Space VM."
  value       = module.confidential_space_instance.instance_external_ip
}

output "server_proxy_url" {
  description = "The Oak Proxy WebSocket URL for connecting to the attested model server."
  value       = "ws://${module.confidential_space_instance.instance_external_ip}:${var.exposed_port}"
}
