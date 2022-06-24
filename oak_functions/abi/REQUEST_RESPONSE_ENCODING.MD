When responding to user requests, the Trusted Runtime applies policies to
prevent information egress.

The policy enforcement layer defines an encoding format for requests and
responses.

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD",
"SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be
interpreted as described in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119).

## Request Encoding

Requests sent by the client are encoded as follows.

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                                                               +
|                              body                             |
+                                                               +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

<!-- Diagram generated with https://www.luismg.com/protocol/, using the schema
"body:96"  -->

### body, variable length byte array

Byte encoded request. Passed to the application layer as is.

## Response Encoding

Responses sent by the client are encoded as follows.

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          status_code                          |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                             length                            +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                                                               +
|                              body                             |
+                                                               +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                            padding                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

<!-- Diagram generated with https://www.luismg.com/protocol/, using the schema
"status_code:32,length:64,body:96,padding:32" -->

### status_code, u32, little endian

Response status as a
[gRPC status code](https://grpc.github.io/grpc/core/md_doc_statuscodes.html).

### length, u64, little endian

The effective length of the body

### body, variable length byte array

For responses with an "Ok" status code the body MUST be the byte encoded
response as received by the application layer. Else the body MUST be a (possibly
empty) UTF-8 encoded developer-facing error message.

### padding, variable length byte array

Trailing 0s the runtime MAY add to ensure responses conform to a fixed size.
