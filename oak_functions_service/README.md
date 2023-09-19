<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-functions-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-functions.svg?sanitize=true"><img alt="Project Oak Functions Logo" src="/docs/oak-logo/svgs/oak-functions.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

`no_std` compatible implementation of the business logic of the Oak Functions
enclave binary.

The interface of the service is defined via microRPC in
[`oak_functions.proto`](/oak_functions_service/proto/oak_functions.proto).

# Lookup

With lookup, a request can trigger private key/value lookups in
`Oak Functions`.

The key idea is that `Oak Functions` initially loads the entire lookup data into
the TEE and requests can then do a key/value lookup on this lookup data.

We want to maintain the following invariants on the key/value lookups.

## Invariant: Consistent view on lookup data

> When the lookup data is updated in the background, key/value lookups of
> requests which arrived after the update will return values from the new lookup
> data, but key/value lookups of requests which arrived before the update will
> return values from the old lookup data.
This means that within a request

- for two key/value lookups of the same key Oak Functions will return the same
  value, and
- the lookup of a key depending on the value of another key share the same view
  of the lookup data.

_Reasoning_: We want a consistent view of the lookup data within the life time
of a request. In the worst case, this can lead to _n_ copies of lookup data for
_n_ requests running in parallel, but we expect short-lived requests and
low-frequency updates of lookup data.

## Invariant: Fully loaded lookup data

> No requests are served until the initial lookup data is completely loaded in
> Oak Functions.
_Reasoning_: If Oak Functions serves requests before it has loaded the complete
lookup data and the key/value pair is not yet loaded, the lookup may falsely
return that no value is found. This is especially problematic, if the lookup
data serves as a block list and no value indicates that the key is not blocked.

## Invariant: At most one value

> Every key has at most one value.
_Reasoning_: This is due to our underlying data structure.

## Invariant: Shared lookup data

> Lookup data can be shared between requests.
_Reasoning_: As we expect large lookup data and short-lived requests, we cannot
afford the space/time to copy lookup data for every request.

## Invariant: Request cannot trigger update

> A request can never trigger the update of lookup data.
_Reasoning_: Updating the lookup data is externally observable. If the
(untrusted) workload running on Oak Functions could trigger the update of lookup
data, it could do so conditional on a secret. The secret could be that the
request looked up a specific key. If the key corresponds to a specific location
this can leak the location of the user.