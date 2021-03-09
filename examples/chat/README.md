# Chat Example

This directory holds a very simple chat application.

All client participants connect to the same Oak server application (one client
creates the application, the other clients connect to the created address:port).

A client then creates a new **room**, which is identified by a random bearer
access token which is needed to join that room and participate in chats there.
The bearer token is used to authenticate the client over gRPC and label messages
sent to that chat room. The room is implicitly created when the first message
with the corresponding label is sent to it.

## Command Line Operation

Initially, the chat example needs to be built, and the server started:

```bash
./scripts/runner --logs run-examples --client-variant=none --example-name=chat
```

After this, one can run the first client, which connects to the Oak Application
and creates a first chat room inside it:

```bash
./scripts/runner --logs run-examples --run-server=false --example-name=chat --client-additional-args=--test=false
```

This will create a file, containing a private key, that the clients need for
authenticating themselves and joining this room. A secure key-sharing mechanism
is required for sharing this key with other parties.

Another party can then join the same chat room by setting `room_secret` to a
path to a file containing the private key:

```bash
./scripts/runner --logs run-examples --run-server=false --example-name=chat --client-additional-args=--test=false --client-additional-args=--room_secret=chat-room.key
```

## CI Invocation

Note that the normal/default invocation of this example (with
`./scripts/runner --logs run-examples --run-server=false --example-name=chat`)
just starts an instance of the application then immediately terminates it (this
ensures that the CI runs work OK).
