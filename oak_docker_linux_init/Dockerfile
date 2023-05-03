FROM alpine:latest
RUN apk add linux-virt alpine-sdk linux-virt-dev \
 alpine-make-vm-image grep coreutils
ADD https://dl-cdn.alpinelinux.org/alpine/v3.17/releases/x86_64/alpine-minirootfs-3.17.3-x86_64.tar.gz \
  /app/alpine-minirootfs.tar.gz
COPY mk_base_initramfs.sh /app/
RUN chmod a+x /app/mk_base_initramfs.sh

