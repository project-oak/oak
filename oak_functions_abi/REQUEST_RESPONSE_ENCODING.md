# Request Response Encoding

When responding to user requests, the Trusted Runtime applies policies to
prevent information egress.

The policy enforcement layer defines an encoding format for requests and
responses. This encoding takes place inside of the end-to-end encrypted channel
established by remote attestation.

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD",
"SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be
interpreted as described in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119).

## Request Encoding

Represents a request sent to an Oak Functions application. It wraps a byte array
that the Wasm module can interpret as a request it can handle.

```text
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

- `body`, variable length byte array

  Represents the response from an Oak Functions application. This is included in
  the body of the HTTP response sent to the client.

## Response Encoding

Responses sent by the client are encoded as follows.

```text
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

- `status_code`, u32, little endian Enum

  ```rust
  Unspecified = 0,
  /// Indicates success of the operation. Similar to HTTP 200 status code.
  Success = 1,
  /// Indicates a problem with the request. Similar to HTTP 400 status code.
  BadRequest = 2,
  /// Indicates violation of the response size limit specified in the security policy.
  PolicySizeViolation = 3,
  /// Indicates violation of the response processing-time limit specified in the security policy.
  PolicyTimeViolation = 4,
  /// Indicates other internal errors at the server. Similar to HTTP 500 status code.
  InternalServerError = 5,
  ```

- `length`, u64, little endian

  The effective length of the body

- `body`, variable length byte array

  For responses with an "Ok" status code the body MUST be the byte encoded
  response as received by the application layer. Else the body MUST be a
  (possibly empty) UTF-8 encoded developer-facing error message.

- `padding`, variable length byte array

  Trailing 0s the runtime MAY add to ensure responses conform to a fixed size.
