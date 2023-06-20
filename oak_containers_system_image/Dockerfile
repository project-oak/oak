FROM clearlinux:base

# Remove .dockerenv as we will not run this image in an actual Docker container.
RUN rm /.dockerenv

# Don't bother starting the graphical interface, let's stick with the basic multi-user target.
RUN rm /usr/lib/systemd/system/default.target
RUN ln -s /usr/lib/systemd/system/multi-user.target /usr/lib/systemd/system/default.target
