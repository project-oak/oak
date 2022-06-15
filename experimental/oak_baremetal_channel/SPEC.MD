# Oak Baremetal Communication Protocol Specification

This document serves as a specification of the protocol used for communication
between the Untrusted Loader and Trusted Runtime. The Trusted Runtime should be
able to communicate with any implementation of the Untrusted Loader that
implements this specification.

In the specification below the Trusted Runtime will henceforth be referred to
the as the "service". The Untrusted Loader will be referred to the as the
"client".

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD",
"SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be
interpreted as described in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119).

### Method

Methods are exposed by the server. They MAY be remotely invoked by the Unrusted
Loader. Each method has clearly defined parameters and return types. The Oak IDL
is used to define which methods are available, their parameter and return types,
as well the protcol used to encode parameters and return values to bytes.

### Invocation

An invocations of a Method. Each invocation consists out of a Request Message
followed by a Response Message.

#### Issuing an invocation

The client MAY issue an invocation by sending a Request Message.

The server MUST NOT send Request Message.

#### Handling an invocation

The server MUST respond to each Request Message with a single Response Message.
It SHOULD respond to Request Messages in first-in-first-out order, but MAY
prioritize some requests. The server MAY issue Response Messages before the
Request Message has been received in its entirety. Sending a Response Messages
concludes the invocation.

The client MUST NOT send Response Messages.

### Messages

A message forms one half of an Invocation.

#### Request Message Fields

A byte encoded request message MUST consist of the following fields:

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                             length                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         invocation_id                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          status_code                          |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                            padding                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                         body bytes...                         +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ ...
```

##### length, u32, little endian

length of the entire message, including this field

##### invocation_id, u32, little endian

Identifies the invocation the request initiates

##### method_id, u32, little endian

identifies the method that is being invoked

##### padding, 4 bytes

reserved to maintain 8 byte alignment. MUST be unset and ignored

##### body, variable length byte array

byte encoded method parameters

#### Response Message Fields

A byte encoded response message MUST consist of the following fields:

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                             length                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         invocation_id                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          status_code                          |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                            padding                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                         body bytes...                         +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ ...
```

##### length u32, little endian

length of the entire message, including this field

##### invocation_id, u32, little endian

MUST match the invocation_id of the relevant Request Message

##### status_code, u32, little endian

response status as a
[gRPC status code](https://grpc.github.io/grpc/core/md_doc_statuscodes.html)

##### padding, 4 bytes

reserved to maintain 8 byte alignment. MUST be unset and ignored

##### body, variable length byte array

For responses with an "Ok" status code the body MUST be the byte encoded method
return value. Else the body MUST be a utf-8 encoded developer-facing error
message.

#### Sending Messages

To send a message, it MUST first be encoded into frames. The resulting frame set
MUST be sent as an uninterrupted sequence.

#### Receiving Messages

To receive a message the recipent incrementally reads frames from the
communication channel. The recipent MAY start parsing a message before all of
its frames have been received.

#### Encoding Messages into Frames

The byte representation of a message MUST be chunked into a set of frame bodies.
The last frame body of the resulting set MAY be shorter than 63,936 bytes (the
maximum size of a frame body). Any preceding frame bodies MUST be exactly 63,936
bytes in length.

A frame MUST then be formed from each frame body.

Messages with a length of 63,936 bytes or less MUST be encoded as a single
frame. In this case the body of the resulting frame contains the entire message.

##### Examples for Illustration

#### Decoding Frames into Messages

Messages are parsed from Frames by appending the frame bodies in the order they
are received.

### Frames

Messages are sent and received as frames. Each message is fragmented into a set
of one or more frames.

#### Frame Fields

A byte encoded frame MUST consist of the following fields:

```
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

##### padding, 4 bytes

for future use

##### length, u16, little endian

Length of the entire frame, including this field. The length of a frame MUST NOT
exceed 64000 bytes

##### flags, two bytes, little endian

###### flags[0]

```
- 7 (MSG): unused
- 6: unused
- 5: unused
- 4: unused
- 3: unused
- 2: unused
- 1: end flag. MUST be set in the last frame of a message
- 0 (LSB): start flag. MUST be set in the first frame of a message
```

###### flags[1]

```
- 7 (MSG): unused
- 6: unused
- 5: unused
- 4: unused
- 3: unused
- 2: unused
- 1: unused
- 0 (LSB): unused
```

##### body, variable length byte array

Byte chunk of an encoded message. In order to not exceed the maximum frame
length, this byte array MUST NOT exceed 63,936 bytes

## Examples for Illustration

### Frame Flags

For messages sent as more than two frames, the first frame would have the start
flag set, all other flags would be unset. The last frame would have the end flag
set, all other flags would be unset. Any frames in between would have no flags
set.

For small messages sent as a single frame, the start flag and the end flag would
be set, all other flags would be unset.

### Layers Diagram

The definition section defines three layers:

- Method Layers: Defines the available methods, parameter and return value
  encoding
- Message Layer: Defines Request Messages and Response Messages
- Frame Layer: Defines how Messages are split into frames

The diagram below shows a practial example of how a method invocation would look
like after being encoded as two frames.

#### Frame 0

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         frame padding                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|          frame length         |          frame flags          |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                 frame body [ message length ]                 |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|              frame body [ message invocation_id ]             |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                frame body [ message method_id ]               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                 frame body [ message padding ]                |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                                                               +
|                                                               |
+   frame body [ message body [ method encoded_parameters ] ]   +
|                                                               |
+                                                               +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ ....
```

#### Frame 1

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         frame padding                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|          frame length         |          frame flags          |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+       frame body [ message body [ method parameters ] ]       +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```
