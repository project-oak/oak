# Oak Baremetal Communication Protocol Specification

This document serves as a specification of the protocol used for communication
between the Untrusted Loader and Trusted Runtime. The Trusted Runtime should be
able to communicate with any implementation of the Untrusted Loader that
implements this specification.

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD",
"SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be
interpreted as described in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119).

## Method

Methods are exposed by the Trusted Runtime. They MAY be remotely invoked by the
Unrusted Loader. Each method has clearly defined parameters and return types.
The Oak IDL is used to define the methods exposed by the Trusted Runtime.

## Invocation

An invocations of a Method. Each invocation consists out of a Request Message
followed by a Response Message.

### Issuing an invocation

The Untrusted Loader MAY issue an invocation by sending a Request Message.

The Trusted Runtime MUST NOT send Request Message.

### Handling an invocation

The Trusted Runtime MUST respond to each Request Message with a single Response
Message. It SHOULD respond to Request Messages in first-in-first-out order, but
MAY prioritize some requests. The Trusted Runtime MAY issue Response Messages
before the Request Message has been received in its entirety. Sending a Response
Messages concludes the invocation.

The Untrusted Loader MUST NOT send Response Messages.

## Messages

A message forms half of an Invocation.

### Request Message Definition

A byte encoded request message MUST consist of the following seqeuential fields:

- length, u32, little endian: length of the entire message, including this field
- invocation_id, u32, little endian: Identifies the invocation the request
  initiates
- method_id, u32, little endian: identifies the method that is being invoked
- padding, 4 bytes: reserved to maintain 8 byte alignment. MUST be unset and
  ignored
- body, variable length byte array: the method’s arguments, encoded with
  flatbuffer

### Response Message Definition

A byte encoded response message MUST consist of the following seqeuential
fields:

- length, u32, little endian: length of the entire message, including this field
- invocation_id, u32, little endian: MUST match the invocation_id of the
  relevant Request Message
- status_code, u32, little endian: response status as a
  [gRPC status code](https://grpc.github.io/grpc/core/md_doc_statuscodes.html)
- status_message_length, u32, little endian: length of the status message
- status_message, utf-8 encoded string: developer-facing error message
- body, variable length byte array: the method’s return value, encoded with
  flatbuffer

### Sending Messages

To send a message, it MUST first be encoded into frames. The resulting frame set
MUST then be send as an uninterrupted sequence.

### Receiving Messages

To receive a message the recipent incrementaly reads frames from the
communication channel. The recipent MAY start parsing a message before all of
its frames have been received.

### Encoding Messages into Frames

The byte representation of a message MUST be chunked. The last chunk MAY be
smaller than 63,984 bytes (the maximum size of a frame body). Any preceeding
chunks MUST be exactly 63,984 bytes in size.

A frame MUST then be formed for each resulting message chunk, with the message
chunk forming the frame body.

Messages smaller 63,984 bytes MUST be encoded as a single frame.

## Frames

Messages are sent and received as frames. Each message can be fragmented into
one or more frames.

### Frame Definition

A byte encoded frame MUST consist of the following seqeuential fields:

- length, u32, little endian: Length of the entire frame, including this field
  The size of a frame MUST NOT exceed 64000 bytes
- flags, two bytes: Bitflags, see [Frame Flags](#3-frame-flags-definition)
- padding, two bytes: reserved to maintain 8 byte alignment
- body, variable length byte array: Byte chunk of an encoded message. In order
  to not exceed the maximum frame size, this byte array MUST NOT exceed 63,984
  bytes

### Frame Flags Definition

- 0x1: MUST be set for frames that are the first of the set that constiutes a
  message
- 0x2: MUST be set for frames that are the last of the set that constiutes a
  message
- 0x3-0x16: Reserved for future use. MUST be unset and ignored
