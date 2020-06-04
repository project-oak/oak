# Node.js client example

To run this client, one first neeeds to install its dependencies by running
`bazel build client` in its directory.

Then start the server of this example from the Oak root:
`./scripts/docker_run ./scripts/run_server -e hello_world`

In another terminal, you can then run this client from its directory:
`npm start`.

If everything works smoothly, you should then find `HELLO Node.js!` logged to
the client's console.
