output "instance_name" {
  description = "The name of the attested Model VM."
  value       = module.confidential_space_instance.instance_name
}

output "internal_ip" {
  description = "The internal IP address of the attested Model VM."
  value       = module.confidential_space_instance.instance_network_ip
}

output "external_ip" {
  description = "The external IP address of the attested Model VM."
  value       = module.confidential_space_instance.instance_external_ip
}

output "self_link" {
  description = "The self-link of the attested Model VM."
  value       = module.confidential_space_instance.instance_self_link
}
