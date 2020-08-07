# HTTP Server Example

This is a simple Oak application that starts an HTTP server. The server responds
with "Hello from HTTP server!\n" to all requests.

This Oak Application has an
[HTTP server pseudo-node](/docs/concepts.md#pseudo-nodes) that connects to a
`StaticHttpServer` that implements
[Node](https://project-oak.github.io/oak/sdk/doc/oak/trait.Node.html).
`StaticHttpServer` is the node serving HTTP requests.
