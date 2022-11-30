# Oak Restricted Kernel Communication Protocol Specification

This document serves as a specification of the protocol used for communication
between the Untrusted Launcher (running on the host) and Enclave Binary built
with the Restricted Kernel (running inside a guest VM).

In the specification below the Enclave Binary will be referred to the as the
"service". The Untrusted Launcher will be referred to the as the "client".

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD",
"SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be
interpreted as described in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119).

## Layer Defintions

Conceptually, the Oak Restricted Kernel Communication Protocol is made up of
three layers. The [Invocation Layer](#invocation-layer) uses protocol buffers
(protobuf) to define the methods exposed by the service. It is responsible for
encoding requests and responses that wrap input parameters and return values.
The [Message Layer](#message-layer) provides a logical wrapper for the encoded
requests and responses. The [Frame Layer](#frame-layer) converts messages into
frames which are then sent over the transport channel.

### Invocation Layer

Methods define the functionality exposed by the service. Each method defines
input parameters and return types. Protocol buffers (protobuf) is used to define
which methods are available, the method ids, input parameters and return types.
The client and service convert the requests and responses into bytes using
standard protobuf encoding.

#### Invocation

Each method invocation consists of two messages: a request message sent by the
client, followed by a response message sent by the service.

##### Initiating an invocation

The client MAY initiate an invocation by sending a request message.

The service MUST NOT send request messages.

##### Handling an invocation

The service MUST respond to each request message with exactly one response
message. The service MAY send a response message before the request message has
been received in its entirety, but MUST NOT start sending a response before any
part of the request message has been received. Sending a response message
concludes the invocation.

The client MUST NOT send response messages.

### Message Layer

Messages are logical units used to transport requests and responses. Each
message consists of an invocation ID, a length and the encoded content of the
request or response it represents.

There are exactly two message types: request messages and response messages.
Since the invocation layer is responsible for encoding requests and reponses, at
the communication protocol level the encoding for request messages and response
messages follows an identical format.

#### Message

The invocation ID and message length is already encoded into the frame, so a
byte encoded message MUST only consist of the encoded bytes:

```text
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                         body bytes...                         +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ ...
```

<!-- Diagram generated with https://www.luismg.com/protocol/, using the spec
"body bytes...:64"  -->

- `body`, variable length byte array

  Encoded byte content of the message.

### Frame Layer

Messages are sent and received as frames with a maximum total length of 4,096
bytes per frame. Each message is fragmented into a set of one or more frames.

#### Frame

A byte encoded frame MUST consist of the following fields:

```text
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          body_length                          |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         message_length                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          frame_number                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         invocation_id                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                         body bytes...                         +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ ...
```

<!-- Diagram generated with https://www.luismg.com/protocol/, using the spec
"invocation_id:32,message_length:32,frame_number:32,body_length:32,body bytes...:64" -->

- `invocation_id`, u32, little endian

  The unique ID of the invocation that the frame's forms a part of. All the
  frames that make up a message MUST have the same invocation ID. The invocation
  ID of a response message MUST match the value of its related request message.
  The invocation ID MUST be incremented for each method invocation, naturally
  wrapping when the maximum value for the data type is reached.

- `message_length`, unsigned 32-bit little-endian integer

  The length of the overall message. This value MUST be larger or equal to
  `body_length`. The message length for all frames that make up the message MUST
  be the same.

  The size of a single message MUST NOT exceed 2GiB.

- `frame_number`, unsigned 32-bit little-endian integer

  The position of this frame within the overall message. The first frame MUST
  start at number 0. Each frame's number MUST be 1 higher than the previous
  frame. Frames for a single message MUST be sent in ascending order of the
  frame number.

- `body_length`, unsigned 32-bit little-endian integer

  The length of the body byte array of the frame. This value must not exceed
  4,080. The sum of the body lengths of all the frames in a message must equal
  the message length.

- `body`, variable length byte array

  Byte fragment of an encoded message. This size of the byte array MUST NOT
  exceed 4,080 bytes.

The maximum total length of a single frame is 4,096 bytes.

## Interaction between the Layers

### Sending Messages

To send a message, the sender MUST first encode the message into frames:

The sender MUST chunk byte representation of the message into a set of frame
bodies. The last frame body of the resulting set MAY be shorter than 4,080 bytes
(the maximum length of a frame body). Any preceding frame bodies MUST be exactly
4,080 bytes in length. The sender MUST then create a frame from each frame body.

The sender MUST send the resulting frame set in sequential order of the frame
number.

### Receiving Messages

To receive a message the recipent incrementally reads frames from the
communication channel. The recipient parses a message from frames by appending
the frame bodies in the order they are received. The recipient MUST validate the
sequence of frame numbers to ensure that all frames are received in the right
order.

The recipent MAY start parsing a message before fully receiving all of its
frames.
