
# Encrypted Echo Example

This example demonstrates a simple echo application running in a
[Confidential Space](https://cloud.google.com/confidential-computing/confidential-space/docs)
environment on Google Cloud. It consists of:

- An enclave application that runs on a GCE confidential VM.
- A client application that communicates with the enclave over an end-to-end encrypted channel.

The communication is secured using the Oak Session Protocol, and the server provides
attestation evidence to the client to prove it's running on genuine confidential hardware and
that the workload has not been tampered with.

This application cannot be run locally, as it requires a connection to the Google Cloud
attestation service to generate endorsements.

## Deploying to Google Cloud Confidential Space

### Prerequisites

1. **Google Cloud Project:** You need a Google Cloud project with billing enabled.

2. **gcloud CLI:** Make sure the `gcloud` CLI is installed and configured.
    - **Authentication:** Log in to your Google account.

        ```bash
        gcloud auth login
        ```

    - **Project Setup:** Set your active project and define a `PROJECT_ID` variable for use in
      later commands.

        ```bash
        gcloud config set project <YOUR_PROJECT_ID>
        export PROJECT_ID=$(gcloud config get-value project)
        ```

        Replace `<YOUR_PROJECT_ID>` with your actual project ID.

3. **Enable GCP APIs:** Enable the required APIs for your project.

    ```bash
    gcloud services enable \
        artifactregistry.googleapis.com \
        compute.googleapis.com \
        confidentialcomputing.googleapis.com
    ```

### 1. Create an Artifact Registry Repository

You need a place to store the container image for the enclave application. Create a Docker
repository in Artifact Registry:

```bash
REPOSITORY_NAME=<YOUR REPOSITORY NAME>

gcloud artifacts repositories create ${REPOSITORY_NAME} \
    --repository-format=docker \
    --location=europe-west1 \
    --description="Echo enclave app repository"
```

Replace `<YOUR REPOSITORY NAME>` with a unique name for your repository.

### 2. Build and Load the Container Image

First, build the OCI image and load it into your local Docker daemon using a single Bazel command:

```bash
bazel run //oak_gcp/examples/echo/enclave_app:load_image
```

### 3. Push the Container Image

Now that the image is loaded locally, you can push it to your Artifact Registry repository.

First, configure Docker to authenticate with Google Artifact Registry:

```bash
gcloud auth configure-docker europe-west1-docker.pkg.dev
```

Then, tag the image and push it:

```bash
docker tag \
    echo_enclave_app:latest \
    europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/echo_enclave_app:latest

docker push europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/echo_enclave_app:latest
```

### 4. Deploy the Confidential VM

Deploy the container image to a GCE Confidential VM. This command will create the VM and start
the workload specified in the `tee-image-reference` metadata field.

By default, the workload will not restart automatically if it stops. If you want it to always
restart, add `~tee-restart-policy=Always` to the `--metadata` flag.

```bash
gcloud compute instances create echo-3ncl4v3-prod \
    --confidential-compute-type=TDX \
    --image-project=confidential-space-images \
    --image-family=confidential-space \
    --maintenance-policy=TERMINATE \
    --metadata="^~^tee-image-reference=europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/echo_enclave_app:latest" \
    --scopes=cloud-platform \
    --zone=us-west1-b
```

#### Create a Firewall Rule

To allow the client to connect to the enclave application, you must open TCP port 8080 on the
firewall.

```bash
gcloud compute firewall-rules create allow-echo-3ncl4v3 \
    --network=default \
    --allow=tcp:8080 \
    --direction=INGRESS \
    --source-ranges=0.0.0.0/0
```

### 5. Test the Deployed Service

Once the VM is running, find its external IP address from the Google Cloud Console or by using
`gcloud compute instances describe`. You can then use the client to connect to it:

```bash
VM_IP=$(gcloud compute instances describe echo-3ncl4v3-prod --zone=us-west1-b --format='get(networkInterfaces[0].accessConfigs[0].natIP)')

bazel run //oak_gcp/examples/echo/client:bin/oak_gcp_examples_echo_client -- \
    --uri="http://${VM_IP}:8080" \
    --request='hello from confidential space'
```

## Debugging

### Server-Side Logging

To see the output from the enclave application (e.g., `println!` statements), you need to deploy
a debug version of the Confidential Space VM and explicitly enable log redirection. This is done
by specifying the `confidential-space-debug` image family and adding the
`tee-container-log-redirect=true` metadata item.

Modify the `gcloud compute instances create` command as follows:

```bash
gcloud compute instances create echo-3ncl4v3-debug \
    --confidential-compute-type=TDX \
    --image-project=confidential-space-images \
    --image-family=confidential-space-debug \
    --maintenance-policy=TERMINATE \
    --metadata="^~^tee-image-reference=europe-west2-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/echo_enclave__app:latest~tee-container-log-redirect=true" \
    --scopes=cloud-platform \
    --zone=us-west1-b
```

The enclave's standard output will be redirected to the VM's serial console and can be viewed in
[Cloud Logging](https://console.cloud.google.com/logs).

### Inspecting Attestation Evidence

The client can save the attestation evidence it receives from the server to a file. This is
useful for offline inspection and verification.

1. **Save the evidence:** Use the `--server-evidence-output-path` flag to specify an output
   file.

    ```bash
    bazel run //oak_gcp/examples/echo/client:bin/oak_gcp_examples_echo_client -- \
        --uri="http://${VM_IP}:8080" \
        --request='hello from confidential space' \
        --server-evidence-output-path=/tmp/evidence.bin
    ```

2. **Inspect the evidence:** The output file is a binary-encoded protobuf. You can use `protoc`
   to decode it into a human-readable text format.

    ```bash
    protoc --decode=oak.attestation.v1.CollectedAttestation \
        proto/attestation/verification.proto < /tmp/evidence.bin
    ```
