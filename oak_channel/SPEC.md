# Oak Baremetal Communication Protocol Specification

This document serves as a specification of the protocol used for communication
between the Untrusted Launcher and Trusted Runtime. The Trusted Runtime should
be able to communicate with any implementation of the Untrusted Launcher that
implements this specification.

In the specification below the Trusted Runtime will henceforth be referred to
the as the "service". The Untrusted Launcher will be referred to the as the
"client".

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD",
"SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be
interpreted as described in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119).

## Layer Defintions

Conceptually, the Oak Baremetal Communication Protocol is made up of three
layers. The [Method Layer](#method-layer) uses the Oak IDL to define the methods
exposed by the service. It is responsible for encoding method parameters and
return values. The [Message](#message-layer) takes encoded parameters / return
values and wraps them as distinct messages that include metadata. The
[Frame](#frame-layer) creates individual frames from messages, which are then
sent over the transport channel.

### Method Layer

Methods define the functionality exposed by service. Each method has clearly
defined parameters and return types. The Oak IDL is used to define which methods
are available, their id, parameter and return types. The Oak IDL is also
responsible for encoding method parameters and return values to bytes.

#### Invocation

An invocation of a method. Each invocation consists of two parts: a request
message sent by the client, followed by a response message sent by the service.

##### Initiating an invocation

The client MAY initiate an invocation by sending a request message.

The service MUST NOT send request messages.

##### Handling an invocation

The service MUST respond to each request message with a single response message.
It SHOULD respond to request messages in first-in-first-out order, but MAY
prioritize some request messages. The service MAY send a response message before
the request message has been received in its entirety. Sending a response
message concludes the invocation.

The client MUST NOT send response messages.

### Message Layer

Messages are conceptual units to transport requests and responses.

There are exactly two messages types: request messages and response messages.

#### Request Message

A byte encoded request message MUST consist of the following fields:

```text
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                             length                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         invocation_id                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                         body bytes...                         +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ ...
```

<!-- Diagram generated with https://www.luismg.com/protocol/, using the schema
"length:32,invocation_id:32,body bytes...:64"  -->

- `length`, u32, little endian

  Length of the entire message, including this field.

- `invocation_id`, u32, little endian

  Identifies the invocation the request initiates.

- `body`, variable length byte array

  Byte encoded method parameters.

#### Response Message

A byte encoded response message MUST consist of the following fields:

```text
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                             length                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         invocation_id                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                         body bytes...                         +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ ...
```

<!-- Diagram generated with https://www.luismg.com/protocol/, using the schema
"length:32,invocation_id:32,body bytes...:64" -->

- `length`, u32, little endian

  Length of the entire message, including this field.

- `invocation_id`, u32, little endian

  MUST match the invocation_id of the relevant request message.

- `body`, variable length byte array

  For responses with an "Ok" status code the body MUST be the byte encoded
  method return value. Else the body MUST be a (possibly empty) UTF-8 encoded
  developer-facing error message.

### Frame Layer

Messages are sent and received as frames. Each message is fragmented into a set
of one or more frames.

#### Frame

A byte encoded frame MUST consist of the following fields:

```text
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                            padding                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|             length            |             flags             |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                         body bytes...                         +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ ...
```

<!-- Diagram generated with https://www.luismg.com/protocol/, using the schema
"padding:32,length:16,flags:16,body bytes...:64" -->

- `padding`, 4 bytes

  For future use.

- `length`, u16, little endian

  Length of the entire frame, including this field. The length of a frame MUST
  NOT exceed 4,000 bytes.

- `flags`, 2 bytes

  - `flags[0]`

    - 7 (MSB): unused
    - 6: unused
    - 5: unused
    - 4: unused
    - 3: unused
    - 2: unused
    - 1: end flag. MUST be set in the last frame of a message
    - 0 (LSB): start flag. MUST be set in the first frame of a message

  - `flags[1]`

    - 7 (MSB): unused
    - 6: unused
    - 5: unused
    - 4: unused
    - 3: unused
    - 2: unused
    - 1: unused
    - 0 (LSB): unused

- `body`, variable length byte array

  Byte fragment of an encoded message. In order to not exceed the maximum frame
  length, this byte array MUST NOT exceed 3,936 bytes.

## Interaction between the Layers

### Sending Messages

To send a message, it MUST first be encoded into frames. The resulting frame set
MUST be sent as an uninterrupted sequence.

### Receiving Messages

To receive a message the recipent incrementally reads frames from the
communication channel. The recipent MAY start parsing a message before all of
its frames have been received.

### Encoding Messages into Frames

The byte representation of a message MUST be chunked into a set of frame bodies.
The last frame body of the resulting set MAY be shorter than 3,936 bytes (the
maximum size of a frame body). Any preceding frame bodies MUST be exactly 3,936
bytes in length.

A frame MUST then be formed from each frame body.

Messages with a length of 3,936 bytes or less MUST be encoded as a single frame.

### Parsing Messages from Frames

Messages are parsed from frames by appending the frame bodies in the order they
are received.

## Examples for Illustration

### Frame Flags

For messages sent as more than two frames, the first frame would have the start
flag set, all other flags would be unset. The last frame would have the end flag
set, all other flags would be unset. Any frames in between would have no flags
set.

For small messages sent as a single frame, the start flag and the end flag would
be set, all other flags would be unset.

### Layers Diagram

The diagram below shows a practial example of how the request half of an
invocation would look like after being encoded as two frames.

#### Frame 0

```text
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         frame padding                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|          frame length         |          frame flags          |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|             frame body [ request_message length ]             |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|          frame body [ request_message invocation_id ]         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|            frame body [ request_message method_id ]           |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|             frame body [ request_message padding ]            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                                                               +
|                                                               |
+   frame body [ request_message body [ method parameters ] ]   +
|                                                               |
+                                                               +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ ...
```

<!-- Diagram generated with https://www.luismg.com/protocol/, using the schema
"frame padding:32,frame length:16,frame flags:16,frame body [ request_message length ]:32,frame body [ request_message invocation_id ]:32,frame body [ request_message method_id ]:32,frame body [ request_message padding ]:32,frame body [ request_message body [ method parameters ] ]:128" -->

#### Frame 1

```text
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         frame padding                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|          frame length         |          frame flags          |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+   frame body [ request_message body [ method parameters ] ]   +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

<!-- Diagram generated with https://www.luismg.com/protocol/, using the schema
"frame padding:32,frame length:16,frame flags:16,frame body [ request_message body [ method parameters ] ]:64" -->
