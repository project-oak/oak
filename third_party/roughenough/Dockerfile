#
# Example multi-stage docker build for running a Roughenough server
#

# Stage 1: build

FROM rust:1.42 AS stage1

ARG ROUGHENOUGH_RELEASE=1.1.7
ARG ROUGHENOUGH_FEATURES="default" 
# Uncomment and replace above if you want KMS support
#ARG ROUGHENOUGH_FEATURES="awskms"
#ARG ROUGHENOUGH_FEATURES="gcpkms"

RUN git clone -b ${ROUGHENOUGH_RELEASE} https://github.com/int08h/roughenough.git \
    && cd /roughenough \ 
    && cargo build --release --features ${ROUGHENOUGH_FEATURES}

# Stage 2: runtime image

FROM gcr.io/distroless/cc

WORKDIR /roughenough

COPY --from=stage1 /roughenough/target/release/roughenough-server /roughenough

# Produce backtraces in case of a panic
ENV RUST_BACKTRACE 1

# Configure Roughenough via environment variables
ENV ROUGHENOUGH_PORT 2002
ENV ROUGHENOUGH_INTERFACE 127.0.0.1
ENV ROUGHENOUGH_SEED 111111111aaaaaaaaa222222222bbbbbbbbb333333333ccccccccc4444444444

# Alternatively Roughenough can use a config file
# COPY roughenough.cfg /roughenough

# How to provide credentials when using GCP KMS
# COPY gcp-creds.json /roughenough
# ENV GOOGLE_APPLICATION_CREDENTIALS /roughenough/creds.json

EXPOSE 2002/udp 

CMD ["/roughenough/roughenough-server", "ENV"]

# Or if using a config file
#CMD ["/roughenough/roughenough-server", "/roughenough/roughenough.cfg"]
