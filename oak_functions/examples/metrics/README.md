# Differentially Private Metrics example

This example show the use of differentially private metrics by the module. The
client repeatedly sends either "a" or "b" to the server. The server reports
event "a" when it receives "a", and does not report any events if it receives
"b".

The resulting exported metrics should provide a relatively accurate count of how
many times 'a' was received, but importantly it should not be possible to
accurately know which of the individual client sessions were 'a' due to the
noise that is added. Even if an attacker knows what was sent in all the requests
except for one, they should not be able to deduce what was sent in the last
request.

The allowed list of events that can be reported, the privacy budget and the
batch size are set in the server configuration file. If multiple different event
labels are allowed, the budget would be evenly split across all of them.

Using a privacy budget value (epsilon) of 1.0 means that approximately 40% of
the time the batch count will be accurate. Approximately 40% of the time it
would be 1 above or below the actual value. The proability of being even further
away from the actual value drops away exponentially from there.

Making the privacy budget larger would increase the probability of an accurate
count, but would reduce the privacy.

The example sends 200 requests alternating between "a" and "b". The batch size
is set to 20, which means that 10 metrics batches will be released.

To run the example, use the following:

```bash
./scripts/docker_run ./scripts/runner \
  --logs \
  run-functions-examples \
  --example-name=metrics
```
