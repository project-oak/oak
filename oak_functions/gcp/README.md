# Deploying Oak Functions to Cloud Run

`api_config.yaml.tempate` is a generic template for the Oak Functions gRPC API.
It can be used to create an instance-specific API Gateway gRPC configuration by
replacing ###TITLE### with an appropriate API title and ###HOST_NAME### with the
host name of the backend Cloud Run instance.

The Weather Lookup Example can be deployed to a Cloud Run backend using:
`/scripts/deploy_oak_functions_loader`

An API Gateway for the backend can be deployed using:
`/scripts/deploy_oak_functions_api`
