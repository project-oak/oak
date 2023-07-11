# Using the same base image that is used in https://github.com/Trusted-AI/adversarial-robustness-toolbox
FROM nvidia/cuda:11.3.1-cudnn8-runtime-ubuntu20.04

# Isntall all required dependencies and packages
RUN apt-get update -y
RUN apt-get install -y python3 python3-distutils python3-pip --no-install-recommends curl

# Note installing keras directly resulted in some issues with saving the model.
RUN pip3 install --no-cache-dir tensorflow==2.12.0

# Install cleverhans for generating adversarial examples.
RUN pip3 install --no-cache-dir cleverhans==4.0.0

# Copy files in the current directory to project.
RUN mkdir /project
WORKDIR /project
COPY . /project

# Download model
RUN curl --output mnist_model.tar.gz  https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:c79e6ba6f862ecbce61237bd2c46b50ab7d7b843b4b999f2c951ec7decbf2230
