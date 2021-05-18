# Oak Functions `key_value_lookup` example

This example shows the simplest nontrivial application of Oak Functions that
uses the key / value lookup functionality.

For each incoming client request, it performs an individual lookup using the
in-memory key / value store, and returns the item, if found, back to the client.
If the item with the provided key is not found, it returns an empty response.

Both request and response are opaque byte arrays.

It is not possible for a client to distinguish between a successful lookup of a
key / value entry in which the value is an empty byte array, and a failed lookup
for which the key was not found at all in the in-memory store.
