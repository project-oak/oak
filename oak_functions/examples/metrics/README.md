# Differentially Private Metrics example

This example show the use of differentially private metrics by the module. The
client repeatedly sends either 'a' or 'b' to the server. The server reportes
event "a" when it receives 'a', and does not report any events if it receives
'b'.

The resulting exported metrics should provide a relatively accurate count of how
many times 'a' was received, but importantly it should not be possible to
accurately know which of the individual client sessions were 'a' due to the
noise that is added. Even if an attacker knows what was sent in all the requests
except for one, they should not be able to deduce what was sent in the last
request.

The allowed list of events that can be reported, the privacy budget and the
batch size are set in the server configuration file. If multiple different event
labels are allowed, the budget would be evenly split across all of them.

To run the example, use the following:

```bash
./scripts/docker_run ./scripts/runner \
  --logs \
  run-functions-examples \
  --example-name=metrics
```
