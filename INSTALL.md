# Step by step instructions for installing Oak on Ubuntu 18.04

This is starting with a clean Ubuntu install. I needed 4 GB of RAM for enclave
creation to work.

```
# apt install git
# apt install docker.io
# apt install curl
# apt install protobuf-compiler
# apt install libprotobuf-dev
# apt install openjdk-8-jdk-headless
# echo "deb [arch=amd64] http://storage.googleapis.com/bazel-apt stable jdk1.8" | tee /etc/apt/sources.list.d/bazel.list
# curl https://bazel.build/bazel-release.pub.gpg | apt-key add -
# apt update
# apt install bazel
# usermod -a -G docker $USER
```

If `$USER` is logged in, you'll need to Log out and log in again (so the group
change takes effect).

We use `rustup` rather than `apt install rustc` because we need `rustup` to add
the webassembly target and it seems that is not in the rustc package.

```
$ curl https://sh.rustup.rs -sSf > /tmp/rustup  # make sure you're happy to run
$ sh /tmp/rustup  # choose option 1
$ rustup target add wasm32-unknown-unknown
$ source $HOME/.cargo/env
$ cd $WHERE_YOU_LIKE_TO_KEEP_GIT_REPOS
$ git clone https://github.com/project-oak/oak.git
$ scripts/run_server_docker  # this may take some time
```

add source $HOME/.cargo/env to your shell init script (e.g. .bashrc or .zshrc)

While you're waiting for docker, you might want to take a look at what that
script does. The one mystery you might run into is: what does Bazel build?

This: `oak/server/BUILD`

In the end, you should end up with an Oak server running.

```
2019-03-20 19:16:36  INFO  oak_driver.cc : 141 : gRPC server started on port 8888
```

Then:

```
$ examples/hello_world/run
```

Which should result in some logs ending with:

```
2019-03-22 06:14:22  INFO  hello_world.cc : 73 : message 0: HELLO WORLD!
2019-03-22 06:14:22  INFO  hello_world.cc : 76 : message 1: HELLO MONDO!
2019-03-22 06:14:22  INFO  hello_world.cc : 79 : message 2: HELLO 世界!
```
