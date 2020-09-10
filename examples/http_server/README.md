# HTTP Server Example

This is a simple Oak application that starts an HTTP server. The server responds
with "Hello from HTTP server!\n" to all requests.

This Oak Application has an
[HTTP server pseudo-node](/docs/concepts.md#pseudo-nodes) that connects to a
`StaticHttpServer` that implements
[Node](https://project-oak.github.io/oak/sdk/doc/oak/trait.Node.html).
`StaticHttpServer` is the node serving HTTP requests.

To run the example interactively:

Run the following command:

```bash
./scripts/runner --logs run-examples --example-name=http_server --client-variant=none
```

In Chrome, install the
[ModHeader](https://chrome.google.com/webstore/detail/modheader/idgpnmonknjnojddfkpgkljpfnnfcklj)
extension (possibly in a dedicated Chrome profile, given the sensitive
permissions it requires).

Click on the ModHeader extension icon, and create a new custom header, with key
`oak-label` and value `{"integrityTags": [], "confidentialityTags": []}`. This
effectively hardcodes a public untrusted IFC label for any subsequent HTTP
request sent to the example Oak Application.

In Chrome, navigate to `https://localhost:8080`. If necessary, skip any warning
related to invalid TLS certificate, as the example uses a self-signed
certificate which is obviously not trusted by the system CA store.

At this point, a welcome message should appear.
