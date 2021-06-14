# Deploying Oak Functions to Cloud Run

`api_config.yaml.tempate` is a generic template for the Oak Functions gRPC API.
It can be used to create an instance-specific API Gateway gRPC configuration by
replacing ###TITLE### with an appropriate API title and ###HOST_NAME### with the
host name of the backend Cloud Run instance.

An Oak Functions Example can be deployed to a Cloud Run backend using:
`/scripts/deploy_oak_functions_loader`

This script requires a number of environment variables. For more details see
`./oak_functions/examples/weather_lookup/scripts/cloud_run_deploy`.

An API Gateway for the backend can be deployed using:
`/scripts/deploy_oak_functions_api`

A Cloud Endpoint for the backend can be deployed using:
`/scripts/deploy_oak_functions_endpoints`
