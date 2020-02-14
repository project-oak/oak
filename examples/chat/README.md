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

The first client to run typically creates the Oak Application and a first chat
room inside it:

```bash
./examples/chat/run
```

This will emit a trace line that holds the information needed to:

- connect to the same Oak application (with `--app_address`)
- join the chat room (with `--room_id`).

```log
2019-10-24 10:47:20  INFO  chat.cc : 242 : Join this room with --app_address=127.0.0.1:32889 --room_id=NKsceNlg69UbcvryfzmFGnMv9qnZ0DYh6u6gJxujnPPxvHsxMehoD368sumKawVaq9WaSkzrcStoNYLvVNdzhA==
```

Another party can then join the same chat room by using these arguments:

```bash
./examples/chat/run -C --app_address=127.0.0.1:32889 --room_id=NKsceNlg69UbcvryfzmFGnMv9qnZ0DYh6u6gJxujnPPxvHsxMehoD368sumKawVaq9WaSkzrcStoNYLvVNdzhA==
```

Alternatively, another party can create a new chat room running on the same Oak
Application by just copying the `--app_address` argument, but specifying a new
room name:

```bash
./examples/chat/run -C --app_address=127.0.0.1:32889
```

This will again emit a trace line with the information needed to join this new
room (on the same server):

```log
2019-10-24 11:04:40  INFO  chat.cc : 242 : Join this room with --app_address=127.0.0.1:32889 --room_id=msSGas1Ie2rtGIvG0bLa2Jh3ODjO35nix46R3j2iYjAcB8zDcJpn/P2DD7c0yB1NMmfoipBSAePJzlXjknm8gg==
```

## CI Invocation

Note that the normal/default invocation of this example (with `./run` or
`scripts/run_example chat`) just starts an instance of the application then
immediately terminates it (this ensures that the CI runs work OK).
