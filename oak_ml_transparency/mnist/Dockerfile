# Using the same base image that is used in https://github.com/Trusted-AI/adversarial-robustness-toolbox
FROM nvidia/cuda:11.3.1-cudnn8-runtime-ubuntu20.04

# Isntall all required dependencies and packages
RUN apt-get update -y
RUN apt-get install -y python3 python3-distutils python3-pip --no-install-recommends curl

COPY requirements.txt /tmp/requirements.txt
RUN pip3 install --no-cache-dir --requirement /tmp/requirements.txt --require-hashes

# Copy files in the current directory to project.
RUN mkdir /project
WORKDIR /project
COPY . /project

# Download the runner
RUN curl --output runner-musl https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha2-256:aa713743ee042da9c481e18d6c031753685c7939e847c27c578129768d1c4e39
RUN chmod +x runner-musl

# Download model
RUN curl --output mnist_model.tar.gz  https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha2-256:63ea4a9906dbbb3a154f069a0d4bc6a2272b9b8151e69fbd57029c826c2cd779
