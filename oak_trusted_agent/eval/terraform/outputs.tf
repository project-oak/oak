output "instance_name" {
  description = "The name of the Confidential Space VM."
  value       = module.confidential_space_instance.instance_name
}

output "results_bucket" {
  description = "The GCS bucket where signed evaluation artifacts are uploaded."
  value       = var.results_bucket_name
}

output "results_gcs_uri" {
  description = "The GCS URI prefix where signed evaluation bundles are uploaded."
  value       = "gs://${var.results_bucket_name}/model-eval/"
}
