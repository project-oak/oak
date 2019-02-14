FROM gcr.io/asylo-framework/asylo:buildenv-v0.3.3
RUN apt-get -y update && apt-get install -y git
