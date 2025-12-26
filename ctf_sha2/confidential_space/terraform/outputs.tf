output "instance_name" {
  description = "The name of the created GCE instance."
  value       = module.confidential_space_instance.instance_name
}

output "instance_network_ip" {
  description = "The internal IP address of the GCE instance."
  value       = module.confidential_space_instance.instance_network_ip
}

output "instance_external_ip" {
  description = "The external IP address of the GCE instance."
  value       = module.confidential_space_instance.instance_external_ip
}

output "instance_self_link" {
  description = "The self-link of the GCE instance."
  value       = module.confidential_space_instance.instance_self_link
}

output "instance_id" {
  description = "The ID of the GCE instance."
  value       = module.confidential_space_instance.instance_id
}
