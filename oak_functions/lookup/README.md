# Lookup

We want to maintain the following invariants on the key/value lookups in the
lookup data loaded into Oak Functions.

## Invariant: Consistent view on lookup data.

When the lookup data is updated in the background, key/value lookups of requests
which arrived after the update will return values from the new lookup data, but
key/value lookups of requests which arrived before the update will return values
from the old lookup data.

In particular, within a request for two key/value lookups of the same key Oak
Functions will return the same value.

_Reasoning_: We want a consistent view of the lookup data within the life time
of a request. In the worst case, this can lead to _n_ copies of lookup data for
_n_ requests running in parallel, but we expect short-lived requests and
low-frequency updates of lookup data.

## Invariant: Fully loaded lookup data.

No key/value lookups of requests are served until the lookup data is completely
loaded in Oak Functions.

_Reasoning_: If Oak Functions serves requests before it has loaded the complete
lookup data and the key/value pair is not yet loaded, the lookup may falsely
return that no value is found. This is especially problematic, if the lookup
data serves as a block list and no value indicates that the key is not blocked.

## Invariant: At most one value.

Every key has at most one value.

_Reasoning_: This is due to our underlying data structure.

## Invariant: Shared Lookup Data.

Lookup Data can be shared between requests.

_Reasoning_: As we expect large lookup data and short-lived requests, we cannot
afford the space/time to copy lookup data for every request.
