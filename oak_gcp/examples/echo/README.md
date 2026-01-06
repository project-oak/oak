# Encrypted Echo Example

This example demonstrates a simple echo application running in a
[Confidential Space](https://cloud.google.com/confidential-computing/confidential-space/docs)
environment on Google Cloud. It consists of:

- An enclave application that runs on a GCE confidential VM.
- A client application that communicates with the enclave over an end-to-end
  encrypted channel.

The communication is secured using the Oak Session Protocol. The server provides
attestation evidence to the client to prove it's running on genuine confidential
hardware. This evidence includes an endorsement of the workload image, signed by
the developer and uploaded to a transparency log, to prove that the workload has
not been tampered with.

This application cannot be run locally, as it requires a connection to the
Google Cloud attestation service to generate endorsements.

## Deploying to Google Cloud Confidential Space

### Prerequisites

1. **Google Cloud Project:** You need a Google Cloud project with billing
   enabled.

2. **gcloud CLI:** Make sure the `gcloud` CLI is installed and configured.
   - **Authentication:** Log in to your Google account. Also, create a set of
     application-default credentials for other commands, like cosign, to use:

     ```bash
     gcloud auth login
     gcloud auth application-default login
     ```

   - **Project Setup:** Set your active project and define a `PROJECT_ID`
     variable for use in later commands.

     ```bash
     gcloud config set project <YOUR_PROJECT_ID>
     export PROJECT_ID=$(gcloud config get-value project)
     ```

     Replace `<YOUR_PROJECT_ID>` with your actual project ID.

3. **Enable GCP APIs:** Enable the required APIs for your project.

   ```bash
   gcloud services enable \
       artifactregistry.googleapis.com \
       cloudkms.googleapis.com \
       compute.googleapis.com \
       confidentialcomputing.googleapis.com
   ```

4. **Generate a Signing Key:** The enclave application must be endorsed by a
   developer key. The client uses the public part of this key to verify the
   endorsement. For a production environment, it is recommended to use a key
   managed by a Key Management Service (KMS).

   Create a keyring and a signing key in
   [Google Cloud KMS](https://cloud.google.com/kms):

   ```bash
   export KEY_RING=echo-enclave-k3y21n9
   export KEY_NAME=echo-enclave-r3l34z3
   export LOCATION=global

   gcloud kms keyrings create "${KEY_RING}" --location="${LOCATION}"

   gcloud kms keys create "${KEY_NAME}" \
       --keyring="${KEY_RING}" \
       --location="${LOCATION}" \
       --purpose=asymmetric-signing \
       --default-algorithm=ec-sign-p256-sha256
   ```

   Your user or service account needs the `Cloud KMS CryptoKey Signer/Verifier`
   IAM role to be able to use the key for signing.

   For initial experimentation, you can also use a local key pair. Note that you
   should never use this approach for a real workload:

   ```bash
   cosign generate-key-pair
   ```

   This will create two files: `cosign.key` (the private key) and `cosign.pub`
   (the public key). You will be prompted for a password to protect the private
   key. The deployment script will ask for this password when signing the
   endorsement.

### 1. Create an Artifact Registry Repository

You need a place to store the container image for the enclave application.
Create a Docker repository in Artifact Registry:

```bash
export REPOSITORY_NAME=<YOUR REPOSITORY NAME>
export REPOSITORY=europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/echo_enclave_app

gcloud artifacts repositories create ${REPOSITORY_NAME} \
    --repository-format=docker \
    --location=europe-west1 \
    --description="Echo enclave app repository"
```

Replace `<YOUR REPOSITORY NAME>` with a unique name for your repository.

### 2. Create a Confidential VM

Next, create a GCE Confidential VM. The deployment tool can then update the VM
to run any new version of the application.

First, create the VM without specifying an image:

```bash
export INSTANCE_NAME=echo-3ncl4v3-prod
export ZONE=us-west1-b

gcloud compute instances create ${INSTANCE_NAME} \
    --confidential-compute-type=TDX \
    --shielded-secure-boot \
    --image-project=confidential-space-images \
    --image-family=confidential-space \
    --maintenance-policy=TERMINATE \
    --scopes=cloud-platform \
    --zone=${ZONE}
```

#### Create a Firewall Rule

To allow the client to connect to the enclave application, you must open TCP
port 8080 on the firewall.

```bash
gcloud compute firewall-rules create allow-echo-3ncl4v3 \
    --network=default \
    --allow=tcp:8080 \
    --direction=INGRESS \
    --source-ranges=0.0.0.0/0
```

#### Managing the VM Instance

You can manage the instance using the following commands.

- **Check the status:**

  ```bash
  gcloud compute instances describe ${INSTANCE_NAME} --zone=${ZONE} --format='get(status)'
  ```

- **Start the instance:**

  ```bash
  gcloud compute instances start ${INSTANCE_NAME} --zone=${ZONE}
  ```

- **Stop the instance:**

  ```bash
  gcloud compute instances stop ${INSTANCE_NAME} --zone=${ZONE}
  ```

- **Reset (reboot) the instance:**

  ```bash
  gcloud compute instances reset ${INSTANCE_NAME} --zone=${ZONE}
  ```

### 3. Build and Deploy the Enclave Application

The example includes a deployment tool that automates the process of building,
pushing, endorsing, and deploying the enclave application to a VM.

Run the deployment tool, providing the repository URI, the KMS key URI, and the
instance details:

```bash
export KMS_KEY="gcpkms://projects/${PROJECT_ID}/locations/${LOCATION}/keyRings/${KEY_RING}/cryptoKeys/${KEY_NAME}"

bazel run //oak_gcp/examples/echo/enclave_app:deploy -- \
    --repository=${REPOSITORY} \
    --cosign-key=${KMS_KEY} \
    --instance=${INSTANCE_NAME} \
    --zone=${ZONE}
```

After you run this command, start or restart the VM to use the new build.

### 4. Test the Deployed Service

Once the VM is running, find its external IP address from the Google Cloud
Console or by using `gcloud compute instances describe`. You can then use the
client to connect to it.

The client needs the public key to verify the enclave's endorsement. Retrieve
the public key from GCP KMS and save it to a file:

```bash
gcloud kms keys versions get-public-key 1 \
    --key=${KEY_NAME} \
    --keyring=${KEY_RING} \
    --location=${LOCATION} \
    --output-file=cosign.pub
```

Now you can run the client:

```bash
export VM_IP=$(gcloud compute instances describe ${INSTANCE_NAME} --zone=${ZONE} \
    --format='get(networkInterfaces[0].accessConfigs[0].natIP)')

bazel run //oak_gcp/examples/echo/client:bin/oak_gcp_examples_echo_client -- \
    --uri="http://${VM_IP}:8080" \
    --request='hello from confidential space' \
    --developer-public-key=$PWD/cosign.pub
```

## Debugging

### Server-Side Logging

To see the output from the enclave application (e.g., `println!` statements),
you need to deploy a debug version of the Confidential Space VM and explicitly
enable log redirection. This is done by specifying the
`confidential-space-debug` image family and adding the
`tee-container-log-redirect=true` metadata item.

Modify the `gcloud compute instances create` command as follows:

```bash
export INSTANCE_NAME_DEBUG=echo-3ncl4v3-debug

gcloud compute instances create ${INSTANCE_NAME_DEBUG} \
    --confidential-compute-type=TDX \
    --shielded-secure-boot \
    --image-project=confidential-space-images \
    --image-family=confidential-space-debug \
    --maintenance-policy=TERMINATE \
    --metadata="tee-container-log-redirect=true" \
    --scopes=cloud-platform \
    --zone=${ZONE}
```

Then, deploy the application to the debug instance:

```bash
bazel run //oak_gcp/examples/echo/enclave_app:deploy -- \
    --repository=${REPOSITORY} \
    --cosign-key=$PWD/cosign.key \
    --instance=${INSTANCE_NAME_DEBUG} \
    --zone=${ZONE}
```

The enclave's standard output will be redirected to the VM's serial console and
can be viewed in [Cloud Logging](https://console.cloud.google.com/logs).

### Inspecting Attestation Evidence

The client can save the attestation evidence it receives from the server to a
file. This is useful for offline inspection and verification.

1. **Save the evidence:** Use the `--server-evidence-output-path` flag to
   specify an output file.

   ```bash
   bazel run //oak_gcp/examples/echo/client:bin/oak_gcp_examples_echo_client -- \
       --uri="http://${VM_IP}:8080" \
       --request='hello from confidential space' \
       --developer-public-key=$PWD/cosign.pub \
       --server-evidence-output-path=/tmp/evidence.bin
   ```

2. **Inspect the evidence:** The output file is a binary-encoded protobuf. You
   can use `protoc` to decode it into a human-readable text format.

   ```bash
   protoc --decode=oak.attestation.v1.CollectedAttestation \
       proto/attestation/verification.proto < /tmp/evidence.bin
   ```
