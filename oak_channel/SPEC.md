# Oak Restricted Kernel Communication Protocol Specification

This document serves as a specification of the protocol used for communication
between the Untrusted Launcher (running on the host) and Enclave Binary built
with the Restricted Kernel (running inside a guest VM). The implemented version
is version 0; version 1 is specified below but has never been implemented.

In the specification below the Enclave Binary will be referred to the as the
"service". The Untrusted Launcher will be referred to the as the "client".

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD",
"SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be
interpreted as described in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119).

## Layer Defintions

Conceptually, the Oak Restricted Kernel Communication Protocol is made up of
three layers. The [Invocation Layer](#invocation-layer) uses microRPC to define
the methods exposed by the service. It is responsible for encoding requests and
responses that wrap input parameters and return values. The
[Message Layer](#message-layer) provides a logical wrapper for the encoded
requests and responses. The [Frame Layer](#frame-layer) converts messages into
frames which are then sent over the transport channel.

### Invocation Layer

Methods define the functionality exposed by the service. Each method defines
input parameters and return types. microRPC is used to define which methods are
available, the method IDs, input parameters and return types. microRPC is also
responsible for encoding method parameters and return values to bytes.

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
concludes the invocation from the perspective of the service.

The client MUST NOT send response messages.

### Message Layer

Messages are logical units used to transport requests and responses. Each
message consists of an invocation ID, a length, and the encoded content of the
request or response it represents.

There are exactly two message types: request messages and response messages.
Since the invocation layer is responsible for encoding requests and reponses, at
the communication protocol level the encoding for request messages and response
messages follows an identical format.

#### Message

Under version 0, MUST consist of a header and a body. The encoded header is 8
bytes long and MUST consist of the following fields:

- `length`, unsigned 32-bit little-endian integer

  The total length of the message including the header and body.

- `invocation_id`, unsigned 32-bit little-endian integer

  The unique ID of the invocation that the message is part of. The invocation ID
  of a response message MUST match the invocation ID of its related request
  message. The invocation ID MUST be incremented for each method invocation,
  naturally wrapping when the maximum value for the data type is reached.

The body contains the encoded bytes of the request or response.

```text
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                            length                             |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         invocation_id                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                         body bytes...                         +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ ...
```

<!-- Diagram generated with https://www.luismg.com/protocol/, using the spec
"length:32,invocation_id:32,body bytes...:64"  -->

### Frame Layer

Messages are sent and received as frames. Each message is fragmented into a set
of one or more frames. The two versions below differ in the frame header, and
with it the maximum length of a frame.

#### Frame

##### Version 0

MUST consist of a header and a body. The encoded header is 8 bytes long and MUST
consist of the following fields:

- `padding`, 4 bytes

  Reserved, and what marks the frame as version 0, since version 1 keeps its
  version number in the first two of these bytes. The sender MUST set every byte
  to zero, and the recipient MUST reject a frame whose padding is anything else.

- `length`, unsigned 16-bit little-endian integer

  The total length of the frame including the header and body. This value MUST
  be larger than 8 (the header length) and MUST NOT exceed 4,000.

- `flags`, unsigned 16-bit little-endian bit field

  | bit | name    | meaning                              |
  | --- | ------- | ------------------------------------ |
  | 0   | `START` | this is the first frame of a message |
  | 1   | `END`   | this is the last frame of a message  |

  All other bits are undefined. The sender MUST leave them clear, and the
  recipient MUST reject a frame that has any of them set.

The body contains the fragment of the encoded message corresponding to the frame
number. The size of the body MUST NOT exceed 3,992 bytes.

Representation of the encoded frame:

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

<!-- Diagram generated with https://www.luismg.com/protocol/, using the spec
"padding:32,length:16,flags:16,body bytes...:64" -->

There is no message length, invocation ID or checksum in the frame header. The
message length and invocation ID are in the [message header](#message); the
frame header is deliberately small because every frame pays for it.

##### Version 1

Specified by earlier revisions of this document, but never implemented. Under
this version the message has no header of its own, because the invocation ID and
message length are in every frame header, and frames belonging to different
messages may be interleaved on one channel and told apart by invocation ID.

MUST consist of a header and a body. The encoded header is 16 bytes long and
MUST consist of the following fields:

- `protocol_version`, unsigned 16-bit little-endian integer

  The version of the communication protocol in use. This value MUST be 1 for
  this version of the specification.

- `frame_length`, unsigned 16-bit little-endian integer

  The total length of the frame including the header and body. This value MUST
  be larger than 16 (the header length) and MUST not exceed 4,096. The sum of
  the frames lengths minus the sum of the header lengths of all the frames in a
  message must equal the message length.

- `message_length`, unsigned 32-bit little-endian integer

  The length of the overall message. This value MUST be larger or equal to the
  frame length minus the header length. The value of this field MUST be the same
  for all frames that make up the message.

- `invocation_id`, unsigned 32-bit little-endian integer

  The unique ID of the invocation that the frame is part of. All the frames that
  make up a message MUST have the same invocation ID. The invocation ID of a
  response message MUST match the invocation ID of its related request message.
  The invocation ID MUST be incremented for each method invocation, naturally
  wrapping when the maximum value for the data type is reached.

- `checksum`, 4 bytes

  The header checksum to detect frame misalignement or other possible header
  corruptions. The checksum MUST be calculated as the truncated SHA-256 hash of
  the first 12 bytes of the header.

  For clarity: the checksum is calculated by appending 20 0 bytes to the end of
  the first 12 bytes of the header, computing the SHA-256 hash of that value and
  taking the first 4 bytes of the result as the checksum.

  The checksum does not cover the body bytes, and it is assumed that the
  application layer is responsible for ensuring the integrity of the content of
  the messages, e.g. through authenticated encryption.

The body contains the fragment of the encoded message corresponding to the frame
number. The size of the body MUST NOT exceed 4,080 bytes.

Representation of the encoded frame:

```text
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|        protocol_version       |          frame_length         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         message_length                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         invocation_id                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                           checksum                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                         body bytes...                         +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ ...
```

<!-- Diagram generated with https://www.luismg.com/protocol/, using the spec
"protocol_version:16,frame_length:16,message_length:32,invocation_id:32,checksum:32,body bytes...:64" -->

The maximum total length of a single frame is 4,096 bytes.

## Interaction between the Layers

This section describes version 0.

### Sending Messages

To send a message, the sender MUST first encode the message into frames:

The sender MUST chunk the byte representation of the message into a set of frame
bodies and prepend an appropriate frame header to each frame body. The sender
MUST set `START` on the first frame and `END` on the last; a single-frame
message has both. The sender MUST send the resulting frame set in sequential
order.

Frames from different messages MUST NOT be interleaved on the same channel: a
frame does not say which message it belongs to, so the only thing that delimits
a message is the run of frames from `START` to `END`.

### Receiving Messages

To receive a message the recipent incrementally reads frames from the
communication channel, appending the frame bodies in the order they are
received, until it reads a frame with `END` set.

The recipient MUST perform the following validation on the frames that make up a
received message:

- the padding of each frame MUST be zero
- the frame length of each frame MUST exceed 8 and MUST NOT exceed 4,000
- no flag bit other than `START` and `END` may be set
- the first frame MUST have `START` set, and no later frame may have it set

If any of these validations fail the recipient MUST treat it as a channel
corruption and stop using the channel for any future communications.
