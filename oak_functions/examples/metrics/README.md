# Differentially Private Metrics example

This example show the use of differentially private metrics by a Wasm module.
The client repeatedly sends either "a" or "b" to the server. The server reports
event "a" when it receives "a", and does not report any events if it receives
"b". A request still counts towards that batch count even if no events are
reported.

The resulting exported metrics should provide a relatively accurate count of how
many times 'a' was received, but importantly it should not be possible to know
which of the individual client sessions sent "a" by looking at the output. Even
if an attacker knows what was sent in all the requests in the batch except for
one, they should not be able to deduce with high certainty what was sent in the
remaining request. The addition of Laplacian noise to the batch counts ensures
this property, assuming appropriate settings are chosen.

The allowed list of event labels, the privacy budget and the batch size are set
in the server configuration file ('config.toml'). If multiple different event
labels are allowed the budget would be evenly split across all of them.

Using a privacy budget value (epsilon) of 1.0 and only one allowed label means
that approximately 39% of the time the batch count will be accurate.
Approximately 19% of the time it would be 1 above and 19% of the time 1 below
the actual value. The probability of being even further away from the actual
value drops away exponentially from there.

Making the privacy budget larger would increase the probability of an accurate
count, but would reduce the privacy. If epsilon is 3.0 the count should be
accurate approximately 78% of the time, which would remove much of the privacy
benefits. With epsilon at 0.1 the count will only be accurate approximately 5%
of the time, but this would provide much stronger privacy.

The noise is independent of the batch size, so making the batch size larger will
improve the relative accuracy without reducing privacy.

The example sends 200 requests alternating between "a" and "b". The batch size
is set to 20, which means that 10 metrics batches will be released and logged.

To run the example, use the following:

```bash
./scripts/docker_run ./scripts/runner \
  --logs \
  run-functions-examples \
  --example-name=metrics
```
