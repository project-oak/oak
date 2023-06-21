FROM clearlinux:base

# Remove .dockerenv as we will not run this image in an actual Docker container.
RUN rm /.dockerenv

# Install Clear Linux's containers-basic bundle. This gives an installation of
# docker to run containers. This is a starting point only, we should switch to
# a more lightweight runtime later.
RUN swupd bundle-add containers-basic

# Configure systemd to run docker at startup
RUN systemctl enable docker

# Don't bother starting the graphical interface, let's stick with the basic multi-user target.
RUN rm /usr/lib/systemd/system/default.target
RUN ln -s /usr/lib/systemd/system/multi-user.target /usr/lib/systemd/system/default.target
