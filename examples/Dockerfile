# hadolint ignore=DL3007
FROM oak_docker:latest

# Name of the compiled Oak application file to copy into the Docker image.
ARG application_file_name

# This runs in the context of each example, e.g. the 'current folder'
# is examples/{current_example}, so we just need the compiled application file from the bin folder
COPY bin/${application_file_name} .
