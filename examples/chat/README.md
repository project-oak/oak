# Chat Example

This directory holds a very simple chat application.

All client participants connect to the same Oak server application (one client
creates the application, the other clients connect to the created address:port).

A client then creates a new **room**, which is identified by a public / secret
key pair:

- the **public key** is used to label messages sent to the room with a
  corresponding confidentiality label, so that only clients that are able to
  authenticate with the corresponding secret key may read them
- the **secret key** is used by each client in order to authenticate to the
  server, so that it may read messages sent by other clients to the same room

Both these keys are also printed as base64 to allow sharing.

In principle, it is also possible to share the public key with external parties,
and therefore have the chat room act as an mailbox to which anyone in possession
of the public key may send messages, but only the holders of the private key may
read them, but the provided client does not show this use case.

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

This will emit a trace line that holds the information needed to:

- connect to the same Oak application (with `--address`)
- join the chat room (with `--room_private_key` and `--room_public_key`).

```log
2019-10-24 10:47:20  INFO  chat.cc : 242 : Join this room with --address=localhost:8080 --room_private_key=NKsceNlg69UbcvryfzmFGnMv9qnZ0DYh6u6gJxujnPPxvHsxMehoD368sumKawVaq9WaSkzrcStoNYLvVNdzhA== --room_public_key=f41SClNtR4i46v2Tuh1fQLbt/ZqRr1lENajCW92jyP4=
```

Another party can then join the same chat room by using these arguments:

```bash
./scripts/runner --logs run-examples --run-server=false --example-name=chat --client-additional-args=--test=false --client-additional-args=--room_private_key=NKsceNlg69UbcvryfzmFGnMv9qnZ0DYh6u6gJxujnPPxvHsxMehoD368sumKawVaq9WaSkzrcStoNYLvVNdzhA==,--room_public_key=f41SClNtR4i46v2Tuh1fQLbt/ZqRr1lENajCW92jyP4=
```

## CI Invocation

Note that the normal/default invocation of this example (with
`./scripts/runner --logs run-examples --run-server=false --example-name=chat`)
just starts an instance of the application then immediately terminates it (this
ensures that the CI runs work OK).
