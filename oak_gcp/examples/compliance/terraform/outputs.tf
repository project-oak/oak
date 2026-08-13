output "anonymizer_public_ip" {
  value       = google_compute_instance.anonymizer_node.network_interface[0].access_config[0].nat_ip
  description = "Public IP address of the Party A Anonymizer enclave."
}

output "anonymizer_internal_ip" {
  value       = google_compute_instance.anonymizer_node.network_interface[0].network_ip
  description = "Internal IP address of the Party A Anonymizer enclave."
}

output "evaluator_public_ip" {
  value       = google_compute_instance.evaluator_node.network_interface[0].access_config[0].nat_ip
  description = "Public IP address of the Party B Evaluator enclave."
}

output "evaluator_internal_ip" {
  value       = google_compute_instance.evaluator_node.network_interface[0].network_ip
  description = "Internal IP address of the Party B Evaluator enclave."
}

output "enclave_service_account" {
  value       = google_service_account.enclave_sa.email
  description = "Service account email used by Confidential Space enclaves."
}

output "artifact_registry_repository" {
  value       = google_artifact_registry_repository.compliance_repo.name
  description = "Artifact Registry Docker repository name."
}
