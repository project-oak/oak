# The MNIST example

This folder contains scripts for building an MNIST model and evaluating it
against adversarial examples. The build script is only included here to make the
example self-contained. The eval script should work with any MNIST model in
[Tensorflow SavedModel format](https://www.tensorflow.org/guide/saved_model).

## Building the Docker image

We use a Docker image, with all the required dependencies installed to build the
model, and run the evaluation. Having such a Docker image is necessary for
achieving transparency. The Dockerfile should include the script for running the
evaluation. More specifically, with the following lines in the Dockerfile, we
embed the evaluation script in the Docker image:

```dockerfile
RUN mkdir /project
WORKDIR /project
COPY . /project
```

Ideally, and as is the case in this example, the Dockerfile and the evaluation
script should belong to the same repository, so that a single Git commit hash
can uniquely specify both the content of the Dockerfile, and the script.

Build the Docker image using the following command:

```bash
cd oak_ml_transparency/mnist
docker build -t mnist-eval .
```

Note that if you make any changes to the script, you have to rebuild the Docker
image for the changes to take effect.

## Run the image

For this example, we run the Docker image in the interactive mode:

```console
$ docker run --tty --interactive --rm \
  --network=host \
  mnist-eval bash
```

This gives us access to a shell:

```bash
==========
== CUDA ==
==========

CUDA Version 11.3.1

Container image Copyright (c) 2016-2023, NVIDIA CORPORATION & AFFILIATES. All rights reserved.

This container image and its contents are governed by the NVIDIA Deep Learning Container License.
By pulling and using the container, you accept the terms and conditions of this license:
https://developer.nvidia.com/ngc/nvidia-deep-learning-container-license

A copy of this license is made available in this container at /NGC-DL-CONTAINER-LICENSE for your convenience.

WARNING: The NVIDIA Driver was not detected.  GPU functionality will not be available.
   Use the NVIDIA Container Toolkit to start this container with GPU support; see
   https://docs.nvidia.com/datacenter/cloud-native/ .

root@hostname:/project#
```

Inspect the directory structure using the `ls` command. You should see that the
`eval.py` script is there:

```console
root@hostname:/project# ls
Dockerfile  README.md  build.py  eval.py  mnist_model.tar.gz runner-musl
```

For development and testing, you can mount the current directory, to run the
code inside the Docker image as you change the script:

```console
$ docker run --tty --interactive --rm \
  --volume=$PWD:/workspace \
  --network=host \
  mnist-eval bash
```

```console
root@hostname:/project# ls /workspace
Dockerfile  README.md  build.py  eval.py
```

## Running the evaluation

Inside the Docker image, we can run the following command to run the evaluation
script on the model:

```bash
python3 eval.py --model=mnist_model.tar.gz --output=result.json
```

Or using the runner:

```bash
./runner-musl \
  --model=mnist_model.tar.gz \
  --model-name=mnist \
  --eval-script=eval.py \
  --output=claim.json
```

## Building the model

You can use the following command to train the model, and save it in the given
path:

```bash
python3 build.py --output mnist-model
```

You can then archive and compress the model into a tar.gz file, and upload it to
a storage, for instance [Ent](https://github.com/google/ent), for future use.

To create the archive file use the following command:

```bash
tar --create --gzip --verbose --file mnist_model.tar.gz mnist-model
```

Note that uploading to Ent requires and API key that you need to acquire out of
band. You also need to install the Ent client and configure it.

Once you have the Ent client, installed and configured, you can use the
following command to upload the tar file:

```bash
./ent put mnist_model.tar.gz
```

The command returns the digest of the file, which you can use for downloading
the file from Ent.

## Pushing to container registry

1. Build the Docker image and tag it with
   `europe-west2-docker.pkg.dev/oak-ci/mnist-eval/mnist-eval`:

   ```bash
   docker build -t europe-west2-docker.pkg.dev/oak-ci/mnist-eval/mnist-eval:latest .
   ```

1. Push to Oak container registry

   ```bash
   docker push europe-west2-docker.pkg.dev/oak-ci/mnist-eval/mnist-eval:latest
   ```

You may need to follow the instructions in
[Oak docker_push script](../../scripts/docker_push) if you run into permission
issues.
