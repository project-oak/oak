# Differentially Private Metrics example

This example shows the use of differentially private count-based metrics by a
Wasm module. Each request to the server contains either "a" or "b". The server
reports event "a" when it receives "a", and does not report any events if it
receives "b", seeing that "b" is not in the list of allowed labels. A request
still counts towards the overall request count even if no events are reported. A
single request can report an event for a single count-based bucket at most once.

The resulting exported metrics should provide a relatively accurate count of how
many requests reported "a", but importantly it should not be possible to know
which of the individual requests sent "a" by looking at the output. Even if an
attacker knows what was sent in all the requests in the batch except for one,
they should not be able to deduce with high certainty what was sent in the
remaining request. The addition of Laplacian noise to the bucket counts ensures
this property, assuming appropriate parameter values are chosen. For more
information on using Laplacian noise in differential privacy, see
https://desfontain.es/privacy/differential-privacy-in-practice.html

The allowed list of metrics buckets (in this case a count-based bucket with
label `"a"`), the privacy budget and the batch size are set in the server
configuration file ('config.toml'). If multiple different buckets are allowed
the budget would be evenly split across all of them.

The probability of a specific integer noise value being added can be calculated
using the cummulative distribution function:

```math
Pr[noise=i] = laplace_cdf(1/epsilon, i + 0.5) - laplace_cdf(1/epsilon, i - 0.5)
```

where (assuming `mu=0`, seeing that we are centering the noise around `0`)

```math
laplace_cdf(beta, x) = 0.5 + 0.5 * sign(x) * (1 - exp(-abs(x) / beta))
```

See https://en.wikipedia.org/wiki/Laplace_distribution for more information.

Using a privacy budget value (epsilon) of 1.0 and only one allowed label means
that approximately 39% of the time the bucket count will be accurate.
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
