FROM gcr.io/distroless/cc
COPY oak_host_loader /root/
COPY oak_enclave_debug.so /root/
WORKDIR /root/
CMD ["./oak_host_loader", "--enclave_path=oak_enclave_debug.so", "--grpc_port=8888"]
