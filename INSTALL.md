# Step by step instructions for installing Oak on Ubuntu 18.04

This is starting with a clean Ubuntu install. I needed 4 GB of RAM for enclave
creation to work.

```bash
apt install git
apt install docker.io
apt install curl
apt install protobuf-compiler
apt install libprotobuf-dev
apt install openjdk-8-jdk-headless
echo "deb [arch=amd64] http://storage.googleapis.com/bazel-apt stable jdk1.8" | tee /etc/apt/sources.list.d/bazel.list
curl https://bazel.build/bazel-release.pub.gpg | apt-key add -
apt update
apt install bazel
usermod -a -G docker $USER
```

If `$USER` is logged in, you'll need to log out and log in again (so the group
change takes effect).

We use `rustup` rather than `apt install rustc` because we need `rustup` to add
the WebAssembly target and it seems that is not in the rustc package.

```bash
curl https://sh.rustup.rs -sSf > /tmp/rustup  # make sure you're happy to run
sh /tmp/rustup  # choose option 1
rustup target add wasm32-unknown-unknown
source $HOME/.cargo/env
cd $WHERE_YOU_LIKE_TO_KEEP_GIT_REPOS
git clone https://github.com/project-oak/oak.git
./scripts/docker_run ./scripts/build_server_asylo  # this may take some time
```

add `source \$HOME/.cargo/env` to your shell init script (e.g. `.bashrc` or
`.zshrc`)

While you're waiting for docker, you might want to take a look at what that
script does. The one mystery you might run into is: what does Bazel build?

This: `oak/server/asylo/BUILD`

Next, build one of the example Applications:

```bash
./scripts/docker_run ./scripts/build_example hello_world
```

After that has built, run the server side of the Application in the Oak Runtime:

```bash
./scripts/docker_run ./scripts/run_server_asylo --application=/opt/my-project/bazel-client-bin/examples/hello_world/config/config.bin
```

In the end, you should end up with an Oak server running.

```log
2020-02-19 10:50:05  INFO  logging_node.cc : 51 : LOG: INFO  sdk/rust/oak/src/lib.rs : 428 : starting event loop
```

Then run the client side of the example (in another terminal):

```bash
./examples/hello_world/run
```

Which should result in some logs ending with:

```log
2020-02-19 10:53:40  INFO  hello_world.cc : 35 : Request: MONDE
2020-02-19 10:53:40  INFO  hello_world.cc : 43 : Response: HELLO MONDE!
2020-02-19 10:53:40  INFO  hello_world.cc : 50 : Request: WORLDS
2020-02-19 10:53:40  INFO  hello_world.cc : 57 : Response: HELLO WORLDS!
2020-02-19 10:53:40  INFO  hello_world.cc : 57 : Response: HELLO AGAIN <default>!

```
