ARG debian_snapshot=sha256:f0b8edb2e4436c556493dce86b941231eead97baebb484d0d5f6ecfe4f7ed193
FROM debian@${debian_snapshot}

COPY ./target/oak_containers_hello_world_trusted_app /usr/bin/

CMD ["/bin/oak_containers_hello_world_trusted_app"]
