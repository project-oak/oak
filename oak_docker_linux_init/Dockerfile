FROM alpine:3.17.3
RUN apk --no-cache add \
  linux-virt=5.15.115-r0 \
  linux-virt-dev=5.15.115-r0 \
  alpine-sdk=1.0-r1 \
  grep=3.8-r1 \
  coreutils=9.1-r0
ADD https://dl-cdn.alpinelinux.org/alpine/v3.17/releases/x86_64/alpine-minirootfs-3.17.3-x86_64.tar.gz \
  /app/alpine-minirootfs.tar.gz
COPY mk_base_initramfs.sh /app/
RUN chmod a+x /app/mk_base_initramfs.sh

