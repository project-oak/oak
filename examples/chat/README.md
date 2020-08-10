# Chat Example

This directory holds a very simple chat application.

All client participants connect to the same Oak server application (one client
creates the application, the other clients connect to the created address:port).

A client can then create a **room**; which returns a pair of random IDs that act
as bearer tokens:

- The **room ID** is needed to join that room and participate in chats there;
  this is printed (as a base-64 string) to allow sharing.
- The **admin ID** allows destruction of the room instance at the server; the
  client keeps hold of this ID internally.

## Command Line Operation

Initially, the chat example needs to be built, and the server started:

```bash
./scripts/runner --logs run-examples --client-variant=none --example-name=chat
```

After this, one can run the first client, which connects to the Oak Application
and opens a first chat room inside it:

```bash
./scripts/runner --logs run-examples --run-server=false --example-name=chat --client-additional-args=--test=false
```

This will emit a trace line that holds the information needed to:

- connect to the same Oak application (with `--address`)
- join the chat room (with `--room_id`).

```log
2019-10-24 10:47:20  INFO  chat.cc : 242 : Join this room with --address=localhost:8080 --room_id=NKsceNlg69UbcvryfzmFGnMv9qnZ0DYh6u6gJxujnPPxvHsxMehoD368sumKawVaq9WaSkzrcStoNYLvVNdzhA==
```

Another party can then join the same chat room by using these arguments:

```bash
./scripts/runner --logs run-examples --run-server=false --example-name=chat --client-additional-args=--test=false --client-additional-args=--room_id=NKsceNlg69UbcvryfzmFGnMv9qnZ0DYh6u6gJxujnPPxvHsxMehoD368sumKawVaq9WaSkzrcStoNYLvVNdzhA==
```

## CI Invocation

Note that the normal/default invocation of this example (with
`./scripts/runner --logs run-examples --run-server=false --example-name=chat`)
just starts an instance of the application then immediately terminates it (this
ensures that the CI runs work OK).
