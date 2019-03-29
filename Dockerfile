FROM gcr.io/asylo-framework/asylo:buildenv-v0.3.3
RUN apt-get -y update && apt-get install -y git curl
RUN curl https://sh.rustup.rs -sSf > /tmp/rustup
RUN sh /tmp/rustup -y
RUN ~/.cargo/bin/rustup target add wasm32-unknown-unknown
