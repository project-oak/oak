# Oak Session Crypto Channel Performance Evaluation

This is a set of communications/crypto channel evaluations for Oak Restricted
Kernel.

It uses a very simple protocol to minimize additional overhead, focusing only on
a basic comms channel and encryption protocol.

We have a simple read/write server implementation for restricted kernel, as well
as for Linux, using a plain TCP socket + our simple protocol.

The underlying protocol is just a length-prefixed blob of bytes.

We currently test the following combinations:

- Plaintext protocol, Local TCP Server (Host)
- NoiseNN encrypted protocol, Local TCP Server (Host)
- NoiseNN **attested**, Local TCP Server (Host)
- TLS, Local TCP Server (Host)
- Plaintext protocol, VM TCP Server
- NoiseNN encrypted protocol, VM TCP Server
- TLS, VM TCP Server
- Plaintext protocol, Restricted Kernel Server
- NoiseNN encrypted protocol, Restricted Kernel Server

The TLS leg is [rustls](https://github.com/rustls/rustls) with the `ring`
provider. It was named after BoringSSL until 2026-08; the code never linked
BoringSSL, and the name is worth keeping straight because "we compared against
BoringSSL" is a different, checkable claim from "we compared against rustls".
BoringSSL is a dependency of this repository, just not of this benchmark.

Most Noise legs are **unattested** NoiseNN (`AttestationType::Unattested`), and
say nothing about DICE or attestation verification cost. One local TCP leg is
attested; see "What attestation costs" below and `attestation.rs`.

All measurements are taken on the host side.

- In general, we are interested in relative latencies rather than absolute
  latencies, so consistency between the test types is important.
- In tests that measure sending speeds, a short ACK from the server is used to
  indicate complete reception of the data.
- In tests that measure receive speeds, the host measures the time it takes to
  receive the expected amount of data.

## What the `Setup` comparison does not show

> [!CAUTION] The `Setup` rows compare two implementations, not two protocols.
> Read on before quoting any Noise-versus-TLS handshake ratio.

**Oak's Noise handshake is almost entirely pure-Rust P-256 scalar
multiplication.** Despite the name, `Noise_NN_P256_AESGCM_SHA256` (see
`oak_crypto/src/noise_handshake/noise.rs`) is P-256, not X25519, and
`crypto_wrapper.rs` implements it with the generic `primeorder` double-and-add
ladder with no assembly. Measured by `p256_cost` in this package:

| operation                                        |     cost |
| ------------------------------------------------ | -------: |
| `P256Scalar::generate`                           |   0.9 µs |
| `compute_public_key` (fixed-base mul)            | 103.3 µs |
| `p256_scalar_mult` (variable-base mul, the `ee`) | 102.5 µs |
| ECDSA sign                                       | 116.0 µs |
| ECDSA verify                                     | 197.6 µs |

The last two rows are not part of the handshake; they are the unit that
attestation is built from, and are used in "What attestation costs" below.

An NN handshake performs four of these in a serial chain -- client keygen, then
server keygen and `ee`, then client `ee` -- for about 412 µs. A transport-free
NN handshake (`//oak_session/benches:benches --bench 'handshake NN'`) measures
417.8 µs, so scalar multiplication is **99% of the compute**, and about 77% of
the ~534 µs measured over local TCP.

Note also that the fixed-base multiplication is not cheaper than the
variable-base one, which means the generator-table optimisation available to
`primeorder` is not in effect. A tuned implementation would make key generation
several times cheaper than ECDH.

**The TLS legs are dominated by a different, unrelated cost.** `cert_gen.rs`
issues an RSA-2048 certificate, so each full handshake includes an RSA
signature. That is the single largest term in the 600-650 µs TLS setup figures,
though it has not been separately measured here.

The consequence is that the near-parity between Noise and TLS setup is a
coincidence of two unrelated inefficiencies, and neither ordering is robust:
re-issue the certificate as ECDSA P-256 and TLS setup falls sharply; give Oak a
tuned P-256 or an X25519 and Noise setup falls sharply. Neither is a
protocol-level result and neither should be presented as one.

Two further asymmetries run in opposite directions, and neither is priced in:

- **The unattested Noise legs authenticate nobody.** They are
  `AttestationType::Unattested` NoiseNN with no static keys, while both TLS legs
  do certificate path building, a signature verification and a hostname check.
  This favours Noise. It is no longer a hand-wave: the attested leg measures
  what Oak's deployable configuration actually costs, and it is **+1.42 ms of
  setup**. See "What attestation costs".
- **Noise setup costs two network round trips to TLS 1.3's one**, because even
  `Unattested` exchanges an AttestRequest and AttestResponse before the
  handshake. On loopback this is tens of microseconds; on a wide-area link it
  doubles time-to-first-byte. This counts against Noise.

## What attestation costs

Oak's attested Noise is _*not*_ a Noise pattern with static keys. It is plain
`NoiseNN` plus a separate attestation step, stitched to the handshake by a
signature over the Noise handshake hash: the responder returns DICE evidence
containing a _session binding_ public key, both sides derive the handshake hash,
and the responder signs that hash with the binding key. Binding a transcript
hash is part of the Noise specification
(<https://noiseprotocol.org/noise.html#channel-binding>), not an Oak invention.
NK and KK are the wrong mental model -- they need pre-distributed static keys or
a PKI, which is exactly what attestation replaces.

The `Local TCP Noise (attested)` leg differs from `Local TCP Noise` only in the
`SessionConfig`. Same transport, same handshake loop, same message count -- an
unattested Oak session still performs the attestation round trip, just with
empty evidence. So the difference between the two legs isolates attestation's
_cryptography and serialisation_, with network shape held constant.

Two runs, `-c opt`, mean one-way latency:

| payload   | Noise unattested |   Noise attested |
| --------- | ---------------: | ---------------: |
| 1 B       |   7.56 / 7.52 µs |   7.57 / 7.59 µs |
| 1000 B    |   8.91 / 8.92 µs |   8.98 / 8.99 µs |
| 16380 B   | 29.71 / 29.80 µs | 29.67 / 29.71 µs |
| 65532 B   | 91.47 / 91.47 µs | 90.78 / 91.40 µs |
| 1 MB      | 1.277 / 1.273 ms | 1.274 / 1.267 ms |
| **Setup** |     509 / 512 µs |   1921 / 1930 µs |

**Attestation costs nothing in steady state and +1.42 ms once, at setup.** Every
message-exchange row agrees between the two legs to within run-to-run variance,
which is the expected result: once the channel is open the two are the same code
operating on the same session keys.

The setup difference decomposes almost entirely into signature operations.
`crypto_channel_attestation_test` pins the shape of the chain -- three DICE
layer certificates plus two application-key certificates -- so this count is
checked rather than asserted:

| operation                           | count |        cost |
| ----------------------------------- | ----: | ----------: |
| client verifies a layer certificate |     3 |    592.8 µs |
| client verifies an application key  |     2 |    395.2 µs |
| client verifies the session binding |     1 |    197.6 µs |
| server signs the handshake hash     |     1 |    116.0 µs |
| **predicted**                       |       | **1302 µs** |
| **measured**                        |       | **1423 µs** |

The 121 µs residual (8.5%) is CBOR/COSE parsing, protobuf serialisation of the
evidence, policy evaluation and the extra bytes on the wire. **91% of
attestation's cost is ECDSA**, at 197.6 µs per verification in pure-Rust P-256
-- the same untuned implementation that dominates the handshake itself.

The ECDSA rows were re-measured after a defect was found in how they were timed:
`verify` returns `Result<(), Error>`, and the benchmark black-boxed the
`unwrap()` of it, which black-boxes a unit and is no optimisation barrier. The
figures moved about 2% when the barrier was made real, which is small enough to
say the verification was always happening, but the earlier 201.7 and 118.6 µs
figures are superseded by these.

This model is fitted to evidence this benchmark generates, so treat it as a
model rather than a measurement. It is, however, corroborated independently.
Walking the recorded Milan DICE chain in `oak_attestation_verification/testdata`
costs 1.02 ms for its five certificates, or 204 µs each, against the 197.6 µs
measured here -- 3.4% apart.

That agreement only appears once the recorded chain is measured correctly.
`verify_cose_sign1_signature` tries the domain-separated AAD first and falls
back to the legacy empty AAD, and **each attempt is a full ECDSA verification**.
Every certificate in `testdata` predates domain separation, so the recorded
chain pays a wasted verification per certificate and reports 2.02 ms rather than
1.02 ms. Current Oak signs layer certificates with `DICE_LAYER_ADDITIONAL_DATA`
(`oak_dice/src/cert.rs`) and application keys with
`APPLICATION_KEYS_ADDITIONAL_DATA` (`oak_attestation/src/dice.rs`), so a current
deployment does not pay it. The figures below are quoted for the current format,
with the legacy cost noted alongside.

> [!WARNING] This leg's client cost is a **lower bound**. The root of trust is
> software, so no AMD SEV-SNP report signature and no VCEK certificate chain are
> verified, and those are ECDSA **P-384**, not P-256.

This host has no TEE. The recorded SEV-SNP evidence in
`oak_attestation_verification/testdata` cannot be substituted, because we do not
hold the private half of its session binding key, so a session using it could
never complete -- the binding signature is exactly what the client checks. What
is measured here is therefore genuine multi-layer DICE with real P-256 keys and
a real binding signature, on a mock root.

Everything above the root is real and is what a real deployment pays. The
missing piece is the root layer alone.

That piece has now been measured, with the benchmarks that already exist in
`oak_attestation_verification`, against the recorded Milan evidence in its
`testdata`:

```bash
bazel run -c opt oak_attestation_verification:benches -- --bench
```

| Verification                                | Current format | Legacy format    |
| ------------------------------------------- | -------------- | ---------------- |
| `verify_attestation_oc` (Oak Containers)    | **2.75 ms**    | 3.74 / 3.78 ms   |
| `verify_attestation_rk` (Restricted Kernel) | **2.33 ms**    | 2.91 / 2.91 ms   |
| `verify_dice_chain_oc` (DICE walk alone)    | **1.02 ms**    | 2.03 / 2.01 ms   |
| `verify_endorsement` (one Rekor log entry)  | 0.61 ms        | 0.600 / 0.614 ms |

The recorded evidence in `testdata` is in the legacy format, so the right-hand
column is what the benchmark prints as checked in. The left-hand column is the
same benchmark with the two AAD attempts tried in the other order, which is what
a peer emitting current-format evidence costs; that ordering was measured on a
throwaway change and is deliberately not part of this stack.
`verify_endorsement` does not go through the DICE COSE path and does not move
between the two columns, which is the control on the comparison.

**A full hardware-rooted Oak Containers verification is 2.75 ms.** This leg
measures 1.92 ms for an attested `Setup` and 0.51 ms unattested.

The client here runs `InsecureAttestationVerifier`. That name is misleading for
costing purposes: what it skips is the _root_, not the chain. It calls
`verify_dice_chain` (`oak_attestation_verification/src/verifiers.rs:403`), which
walks every layer certificate and then `verify_application_keys`, so the
attested `Setup` already pays a full five-certificate chain walk. It returns
`extracted_evidence: None` only because the last layer's certificate authority
key signs nothing.

That is what the 1.42 ms attested-minus-unattested delta decomposes into. The
prediction below uses only primitives measured in a _different_ harness, so it
is a real check and not an accounting identity:

| Component                                        | Count |         Cost |
| ------------------------------------------------ | ----: | -----------: |
| DICE chain walk, at `p256_cost` verify           |     5 |     0.988 ms |
| session binding, sign + verify                   |   1+1 |     0.314 ms |
| **predicted**                                    |       | **1.302 ms** |
| **measured**                                     |       |  **1.42 ms** |
| residual: CBOR/COSE, protobuf, policy, transport |     — |     0.118 ms |

ECDSA is 92% of the delta, and the 8.3% residual is the part the model does not
account for.

So a real SEV-SNP root **adds the platform and firmware verification only** --
2.75 − 1.02 = **1.73 ms**, roughly three P-384 verifications for the report
signature and the ARK → ASK → VCEK chain -- and does not add the chain walk a
second time. The attested `Setup` would go from 1.92 ms to about **3.65 ms**, or
**5.8x the rustls handshake** (0.633 ms), against the ~3.0x measured here.

> [!CAUTION] An earlier revision of this file said the insecure verifier
> performs "no chain verification at all" and projected **4.7 ms** and **7x**.
> That was wrong, on the strength of reading `extracted_evidence: None` as
> meaning no work was done. The correct figures are 3.65 ms and 5.8x. The
> revision before _that_ projected ~4.5 ms by subtracting
> `verify_attestation_software_rooted`, which was also wrong, because that
> benchmark walks a three-certificate chain rather than this leg's five. Both
> earlier numbers are withdrawn.

That 3.65 ms is a **projection, not a measurement**. It assumes nothing else
changes -- in particular that transporting real SEV-SNP evidence and
endorsements costs the same as transporting the standalone ones, which is
unlikely to be exactly true because the real blob is larger. Quote it as
approximate. An end-to-end attested session against a real SEV-SNP machine is
the measurement that would settle it, and this host cannot make one.

The `verify_endorsement` row is listed separately because the 2.75 ms does
**not** contain it. Removing the event log policies from the Oak Containers
verifier changes the total from 3.73 ms to 3.71 ms in the legacy column, which
is inside the noise, so with these recorded reference values nothing in that
figure verifies a transparency-log entry. A deployment that requires
Rekor-backed endorsements pays about 0.6 ms per endorsed layer on top. See
`verify_attestation_oc_platform_and_firmware` in the same benchmark file.

Reference values are `SkipVerification`, so the policies parse and traverse the
evidence without comparing measurements against expected digests. That
comparison is a handful of digest equality checks and is not where the time
goes.

## The allocator, and why the large payloads used to move

> [!WARNING] Every large-payload figure in this file, and every figure in any
> revision of this file before 2026-08-28, was taken without controlling the
> allocator, and depended on which benchmarks had run earlier in the same
> process.

The symptom was two legs running byte-identical post-handshake code disagreeing
by 2.3x at a 1 MB payload. The same unattested Noise leg measured:

| context               |      1 MB result |
| --------------------- | ---------------: |
| full sweep, ran first |   2.97 / 3.00 ms |
| filtered to >= 100 kB | 1.266 / 1.271 ms |

The harness allocates per iteration -- `send_message` builds a fresh frame, and
the Noise path adds a `to_vec()`, a protobuf `encode_to_vec()` and a read buffer
-- so at large payloads each exchange allocates and frees several multi-megabyte
blocks, and the measurement is substantially an allocator benchmark.

glibc's mmap threshold is adaptive: it starts at 128 kB and ratchets upward each
time an mmap'd block is freed. Setting it via the tunable also sets
`no_dyn_threshold`, which freezes the **trim** threshold at its 128 kB default,
so the heap is handed back to the kernel and re-faulted on the next iteration.
That, not mmap, is the mechanism. Measured at a 1 MB payload:

| configuration                      | Plaintext |    Noise |
| ---------------------------------- | --------: | -------: |
| default (adaptive)                 |   99.7 µs |  1.27 ms |
| `MMAP_THRESHOLD_` pinned high only |    577 µs |  3.12 ms |
| `MMAP_THRESHOLD_` pinned low only  |    790 µs |  3.91 ms |
| **both thresholds pinned high**    |    101 µs | 1.275 ms |

Pinning both restores the adaptive default's converged value at every payload
measured, which is what identifies the trim threshold as the cause. The
benchmark now pins both, so the result no longer depends on ordering; see the
`env` attribute on the `benchmark` target and the comment there.

The per-byte marginal cost above is derived from the 16380 and 65532 points, and
only one of those was safe. 16380 is insensitive: it agrees to within 1% across
all four configurations. 65532 is _*not*_ -- it reads 91.5, 141.7 and 193.8 µs
for Noise across the three uncontrolled configurations.

What rescues the figure is that 65532 was nevertheless stable under the
_default_ allocator across every ordering tried (91.0-91.8 µs over five
measurements), and the pinned configuration reproduces that same value. So the
published number did not change. That is luck rather than design, and it is
worth stating plainly: measured under the two artificial configurations the
Noise figure would have been 9.87 or 11.08 cycles per byte instead of 5.10, and
"3.5x rustls" would have been written as "6.9x" or "7.4x".

## What the `Message Exchange` comparison shows, by payload size

Until 2026-08-28 this group was measured at a **single 1-byte payload**, and
every per-message claim in this file was read off that one point. It was the
wrong point to choose, in a way that flattered Oak.

At 1 byte an exchange is almost entirely fixed cost. Every leg issues two socket
writes per exchange, and several reads, at roughly 1 us a call on this host. The
Noise legs put **89 bytes** on the wire to carry 1 byte, because the session
layer wraps the payload in a protobuf, against about 26 for a TLS record.
Nothing in that row is cryptography.

The sweep was measured twice. The first measurement is **retracted**: the two
added sizes were `16_384` and `65_536`, but `send_message` puts the 4-byte
length prefix in the same write, so rustls saw `payload + 4` and fragmented --
`16_384` was the _worst_ point rather than the record boundary it was documented
as. In the same measurement the read buffer sat _below_ rustls, where it
coalesced rustls's own 4 KiB record reads and so removed socket calls a real
rustls user would pay. Both are fixed; see `TEST_SIZES` and
`new_tls_client_stream` in `benchmark.rs`.

Two runs, `-c opt`, mean one-way latency in microseconds. Measured with the
allocator tunables pinned; see "The allocator, and why the large payloads used
to move" below, and note that the numbers below supersede an earlier set taken
before that defect was understood:

| Payload | Plaintext     | Noise         | Noise (attested) | TLS (rustls)  |
| ------- | ------------- | ------------- | ---------------- | ------------- |
| 1 B     | 6.81 / 6.83   | 7.56 / 7.52   | 7.57 / 7.59      | 7.59 / 7.58   |
| 1000 B  | 7.03 / 7.00   | 8.91 / 8.92   | 8.98 / 8.99      | 8.02 / 8.05   |
| 16380 B | 11.12 / 11.13 | 29.71 / 29.80 | 29.67 / 29.71    | 20.79 / 20.66 |
| 65532 B | 19.46 / 19.53 | 91.47 / 91.47 | 90.78 / 91.40    | 44.50 / 44.05 |

Every point reproduces to about 1%. That includes the 1-byte row, which did
_not_ reproduce in the first measurement: Noise moved 19% between runs and in
the second run came out above its own 1 KiB figure, which is not physically
possible. The "about 1.6x per message" figure this file carried earlier, which
was read off that row, is retracted. Two runs agreeing is not a demonstration
that the instability is gone, so treat the 1-byte row as provisional.

Correcting the buffer placement moved the TLS leg the unfavourable way for Oak:
at 16 KiB rustls went from 18.40 us to 20.79 us, because it now pays its own
socket reads.

Taking the marginal cost between the 16380 and 65532 points, which cancels the
fixed cost, and converting at the measured 4.6927 GHz:

| Leg              | Marginal cost per byte, net of plaintext |
| ---------------- | ---------------------------------------- |
| TLS (rustls)     | 1.47 / 1.43 cycles                       |
| Noise            | 5.10 / 5.09 cycles                       |
| Noise (attested) | 5.04 / 5.09 cycles                       |

So at this size Oak's Noise data path costs about **3.5x rustls per byte** once
the framing and syscall floor is subtracted, and attestation does not change
that -- the attested and unattested legs agree to within run-to-run variance,
because attestation is a setup cost only. The ratio is not constant in payload
size; see below.

### The larger payloads, and how much they can be trusted

The sweep also covers the four decade sizes this group has always measured. They
are kept because they are the only points that leave cache, but they are
reported separately because they are the points the allocator defect below was
found at, and because the largest of them is not stable enough to quote to three
digits. Two runs, `-c opt`, allocator pinned:

| Payload | Plaintext        | Noise            | Noise (attested) | TLS (rustls)     |
| ------- | ---------------- | ---------------- | ---------------- | ---------------- |
| 100 kB  | 20.97 / 21.13 µs | 130.9 / 131.4 µs | 131.6 / 131.1 µs | 54.42 / 54.43 µs |
| 1 MB    | 96.14 / 97.33 µs | 1.277 / 1.273 ms | 1.274 / 1.267 ms | 337.1 / 338.0 µs |
| 10 MB   | 1.641 / 1.628 ms | 14.56 / 14.11 ms | 14.53 / 14.24 ms | 3.850 / 3.914 ms |
| 100 MB  | 28.50 / 27.12 ms | 241.7 / 220.1 ms | 241.7 / 213.8 ms | 45.17 / 43.44 ms |

Reproducibility degrades with size: 100 kB and 1 MB agree between runs to about
1%, 10 MB to about 3%, and 100 MB to between 4% and 12% depending on the leg.
**Do not quote the 100 MB row to better than about 10%.** Criterion's own
confidence intervals on that row are much tighter than the spread between runs,
so they understate the uncertainty; the run-to-run spread is the honest figure.

Taking the same marginal cost as above, but between each consecutive pair of
sizes rather than only the first pair, the per-byte cost is not constant across
the range:

| Interval           | Noise        | TLS (rustls) | Ratio |
| ------------------ | ------------ | ------------ | ----- |
| 16380 B -> 65532 B | 5.10 / 5.09  | 1.47 / 1.43  | 3.5x  |
| 65532 B -> 100 kB  | 5.16 / 5.21  | 1.15 / 1.19  | 4.5x  |
| 100 kB -> 1 MB     | 5.58 / 5.55  | 1.08 / 1.08  | 5.2x  |
| 1 MB -> 10 MB      | 6.12 / 5.89  | 1.03 / 1.07  | 5.8x  |
| 10 MB -> 100 MB    | 10.44 / 9.41 | 0.75 / 0.73  | 13x   |

Cycles per byte at 4.6927 GHz, net of plaintext, two runs. The last row carries
the 100 MB row's uncertainty, so read it as "about 10 against about 0.75", not
to three digits.

Noise gets worse with size while rustls gets better. That is consistent with the
Noise path making more full-buffer copies -- `to_vec()` in `noise.rs` and the
protobuf `encode_to_vec()` in the session layer -- so that once the working set
exceeds the 32 MiB L3 each copy costs DRAM bandwidth instead of cache bandwidth,
whereas rustls encrypts in place into a buffer it reuses. That mechanism is
**not isolated here**; it is the hypothesis a profile would have to confirm or
kill. The 3.5x headline figure is the one taken between 16380 and 65532 bytes,
which is the most reproducible interval, and it is the most favourable to Oak of
the five.

defects in this group both were. Counted with `strace -c -f` at a 65532-byte
payload, self-calibrated against a run whose `--bench` filter matched nothing,
and divided by an exact exchange count taken from a counter compiled into the
timed loop for the measurement:

| Leg       | Writes/exchange  | Reads/exchange |
| --------- | ---------------- | -------------- |
| Plaintext | 2.000 (`sendto`) | 4.000          |
| Noise     | 2.000 (`sendto`) | 4.000          |
| TLS       | 2.000 (`writev`) | **16.000**     |

rustls deframes in 4 KiB chunks, so 65540 bytes costs eight reads per side. The
TLS legs pay **twelve more** socket calls per exchange than Noise and are still
2.05x faster. Crediting TLS the full ~1 us per extra call, about 12 us, narrows
the 47 us gap at this payload only to about 35 us. The syscall asymmetry runs
against TLS, so it cannot be what makes Noise slow.

Likely causes, none of them yet isolated: `oak_crypto` builds a fresh
`Aes256Gcm` key schedule per message and calls `ChaCha20Rng::from_entropy()` per
nonce
([crypto_wrapper.rs](../../../oak_crypto/src/noise_handshake/crypto_wrapper.rs)),
the Noise layer copies each ciphertext into a new `Vec`
([noise.rs](../../../oak_crypto/src/noise_handshake/noise.rs)), and the session
layer serialises through protobuf. The first two are fixed costs and cannot
explain a per-byte gap; the copies and the protobuf can. The TLS legs install
`rustls::crypto::ring::default_provider` (see `init_rustls` in
`linux_server.rs`), so their AES-GCM is ring's assembly implementation on AES-NI
and CLMUL. Confirming which of these dominates needs a profile, and that has not
been done.

## What each group measures

Every leg reports two groups.

| Group suffix           | Timed region                                |
| ---------------------- | ------------------------------------------- |
| `... Message Exchange` | one send and one receive on an open channel |
| `... Setup`            | transport connect plus the leg's handshake  |

`Message Exchange` reports `(send + recv) / 2`, a **mean one-way latency, not a
round trip**. Do not quote it as an RTT.

`Setup` is the metric the evaluation plan calls handshake latency. On the TCP
legs the plaintext leg has no handshake, so its `Setup` figure is the transport
cost alone and is the floor the other legs on that transport are read against.

> [!WARNING] That does _*not*_ hold for the restricted-kernel legs.
> `OakClientChannelMessageStream::new` is an `Rc::clone`, so
> `RK Plaintext Setup` times a refcount bump rather than a transport. It is not
> a floor, and subtracting it from `RK Noise Setup` charges Noise for the
> enclave channel round trips the plaintext row never performs.

The two groups are the two arms the evaluation plan asks for: `Message Exchange`
holds **one channel open** for the whole measurement, `Setup` performs a
**handshake per iteration**. The per-RPC cost of a protocol that reconnects each
time is the sum of the two; the cost for a protocol that keeps a channel is
`Message Exchange` alone.

### The settle interval between `Setup` iterations

Between iterations `Setup` closes the channel and then waits `SETUP_SETTLE` (200
µs), both untimed. Without that wait, a connect issued while the previous
connection's teardown is still in flight is markedly slower, which doubled the
plaintext figure and left its confidence interval at ±23%.

Sweeping the interval on the local TCP leg with everything else held constant:

| interval | reported plaintext setup |
| -------: | -----------------------: |
|     0 µs |           33.34 µs, ±22% |
|    10 µs |                 23.84 µs |
|    25 µs |                 18.02 µs |
|    50 µs |                 17.22 µs |
|   300 µs |          16.78 µs, ±1.3% |
|   600 µs |                 18.31 µs |
|  1000 µs |                 19.37 µs |

The curve has a threshold rather than a slope: almost all of the effect is
recovered by 25 µs and nothing further after that. Two mechanisms were ruled
out. It is _*not*_ the listen backlog -- the kernel completes a loopback connect
without the server calling `accept`. And it is _*not*_ ephemeral-port or
`TIME_WAIT` pressure -- sweeping `TIME_WAIT` occupancy from 36 to 87,084 sockets
moves the figure by 0.7%, and the faster runs hold more sockets in `TIME_WAIT`
than the slower ones.

25 µs is about one loopback round trip on the host this was measured on, which
is suggestive but _*not*_ established as a scaling law: the threshold was only
ever measured on the local TCP leg. 200 µs deliberately over-provisions, which
is safe either way. If the threshold does track the round trip, the VM legs run
at roughly 33 µs one way, so ~70 µs, and 200 µs clears that with 2.6x margin --
a 50 µs value tuned on the local leg would have left them contaminated.

#### What the interval costs

It is not free for the legs that do real work in the handshake. Measured back to
back in one session, so that day-to-day drift is not in the comparison:

| leg       |           0 µs |          50 µs |                 200 µs |
| --------- | -------------: | -------------: | ---------------------: |
| plaintext |   33.35, 33.97 |   16.30, 15.93 |    16.42, 16.46, 16.80 |
| Noise     | 530.00, 527.46 | 530.79, 532.94 | 533.98, 536.71, 530.58 |
| TLS       | 176.05, 174.48 | 182.02, 177.43 | 180.27, 179.39, 178.34 |

TLS costs about 2% and Noise about 1%, the latter inside the run-to-run spread.
The penalty is **flat between 50 µs and 200 µs**, so it is a threshold rather
than something proportional to the length of the spin. That rules out the spin's
duty cycle depressing the boost clock, and points instead at the server thread
having gone idle between iterations, so the timed handshake now includes waking
it.

The same mechanism is the best available explanation for the upturn at 600 µs
and beyond: the client core is busy-spinning throughout, so it is not the client
that idles -- the longer the client waits, the deeper the idle state the server
thread reaches, and the more its wake-up costs. This is an inference from the
shape of the two tables rather than something measured directly; the server's
C-state residency has not been instrumented.

That is a reason to keep the interval rather than shorten it: a server that has
to be woken is the more representative case, since a real one is not spinning in
wait for the next connection. The trade is 2% on one leg against a plaintext
baseline that was otherwise twice its true value at ±23%.

> [!NOTE] If the interval is too short for a leg, that leg's confidence interval
> stays wide, so narrowing is good confirmation. The converse does _*not*_ hold:
> a VM leg can have a wide interval for reasons unrelated to this setting -- see
> QEMU's user-mode networking churn below -- so a persistently wide VM interval
> is not by itself evidence that the settle is too short. Vary the settle on
> that leg before concluding anything.

`Message Exchange` used to open a fresh channel per iteration too, untimed. That
excluded the connect from the reported figure but not from the machine, and it
mattered most where it was least affordable: on the VM legs the resulting
connection churn through QEMU's user-mode networking left two of six points with
confidence intervals spanning more than an order of magnitude, and made
plaintext look slower than both encrypted legs. Holding the channel open also
cut the local figures by 14-24%.

### The control protocol

The servers are echo servers, so a client needs a way to say it is finished. Two
sentinels, defined in `message_stream::control`:

| Sentinel   | Meaning                                                                                                                      |
| ---------- | ---------------------------------------------------------------------------------------------------------------------------- |
| `b"close"` | Finish with this channel. Echoed back, then the server returns to `accept` (or, in the enclave, discards its Noise session). |
| `b"exit"`  | Shut the server down. Not echoed.                                                                                            |

`close` is acknowledged rather than being a bare disconnect because the
Restricted Kernel leg has no connection to close: without the reply the enclave
would sit reading an application message while the client sent the first frame
of a new handshake. Benchmark payloads cannot collide with either sentinel,
since `create_message` fills a buffer with `0, 1, 2, ...`.

A client that disconnects without saying `close` is tolerated -- the server
treats end-of-stream as the end of that connection. It has to, because the
server outlives every client and a panic on the server thread would surface
later against an unrelated leg.

> [!IMPORTANT] Until 2026-08 the TLS leg's handshake was charged to its first
> timed send. `rustls::StreamOwned::new` does not handshake; rustls defers it to
> first use, and nothing forced it earlier. The Noise leg, whose handshake
> happens eagerly in `NoiseMessageStream::new_client`, was not charged for its
> own. The legs were not measuring the same thing. `new_tls_client_stream` now
> calls `complete_io` so the handshake lands in `Setup` on every leg. Removing
> it from the timed send cut the reported TLS exchange latency by about half.

## Nagle's algorithm

> ⚠️ **IMPORTANT**: Use `linux_server::connect` for any new leg, never
> `TcpStream::connect`.

Until 2026-08 every socket here ran with Nagle's algorithm enabled. The
length-prefixed framing writes the 4-byte prefix and the body as two separate
writes, so the body waited on the peer's 40 ms delayed-ACK timer. It did not hit
the legs evenly, and it **inverted the result**. Local TCP, 50 samples per
point:

| Group                      |    Nagle | `TCP_NODELAY` |  change |
| -------------------------- | -------: | ------------: | ------: |
| Plaintext Message Exchange | 13.01 us |      13.03 us |       - |
| Plaintext Setup            | 36.83 us |      33.77 us |       - |
| Noise Message Exchange     | 22.83 ms |      13.58 us | -99.94% |
| Noise Setup                | 91.68 ms |     529.81 us | -99.42% |
| TLS Message Exchange       | 52.66 us |      19.56 us |  -62.9% |
| TLS Setup                  | 172.9 us |     172.88 us |       - |

Plaintext escaped because its connections carry a single exchange, so no
unacknowledged segment ever precedes the write. Noise took the full stall on
every message.

**Correction.** This paragraph used to explain rustls's smaller penalty by
saying it "coalesces a record into one write rather than two". That is wrong.
`rustls::StreamOwned::write` forms a record and then calls `complete_io`, so
before the framing fix each of the two writes produced its own record and its
own socket write, exactly as on the Noise leg. Why rustls suffered less than
Noise under Nagle is unexplained.

> [!NOTE] The `Setup` rows above predate `SETUP_SETTLE`. Both columns were
> measured without the settle interval, so the comparison between them is sound,
> but the absolute plaintext `Setup` figure is roughly double what the current
> harness reports. It is now about 16.4 us rather than 33.77 us.

Read against the corrected figures, the Noise data path costs 4% over plaintext
and beats rustls by 1.4x on the message-exchange arm. Both of those numbers have
since been superseded; see the warning below.

> [!WARNING] Two corrections apply to the figures above.
>
> **The 1.4x is retracted, and its sign was wrong.** It was measured while the
> framing charged rustls two TLS records per message, and while the raw legs
> issued an extra socket read that TLS did not. With both artefacts removed the
> message-exchange arm reads plaintext 6.94 µs, rustls 7.40 µs, Noise 7.67 µs.
> See `BufferedStream` and `send_message` in `message_stream.rs`.
>
> Those three figures are all at a **1-byte** payload, and that row was
> irreproducible when it was first swept -- see
> [What the `Message Exchange` comparison shows, by payload size](#what-the-message-exchange-comparison-shows-by-payload-size).
> Do not replace "beats rustls by 1.4x" with any other single ratio drawn from
> it. Read the sweep instead: from 1000 bytes upward Noise costs 1.8x to 2.9x
> the TLS overhead over plaintext, and about 3.4x per byte at the margin.
>
> This section also used to add "while Noise setup is 3.1x slower than a rustls
> handshake". **That was wrong.** The rustls leg was resuming its TLS sessions
> -- one `ClientConfig` was shared across every iteration and
> `Resumption::default()` is an in-memory store of 256 sessions, so only the
> first handshake was full. A resumed handshake sends no certificate and
> generates no signature. With resumption disabled the rustls handshake costs
> ~652 us against Noise's ~534 us, so **Noise setup is about 1.2x faster, not
> 3.1x slower**. See `tls_client_config` in `benchmark.rs`.

`linux_server::connect` and `start_tcp_server` now set `TCP_NODELAY`, and
`linux_server_test` covers both call sites. The root cause is the two-write
framing in `message_stream.rs`; fixing it there would also help the Restricted
Kernel channel, which is not a socket.

## Running VM TCP Benchmarks

The VM TCP benchmarks require a VM running the `crypto_channel_server` binary.
The server serves all three protocols simultaneously on different ports:

| Protocol  | Default Port |
| --------- | ------------ |
| Plaintext | 5000         |
| Noise     | 5001         |
| TLS       | 5002         |

### Prerequisites

Install the required tools:

```bash
sudo apt install libguestfs-tools qemu-system-x86
```

### Option A: Using Bazel (Recommended)

1. Build the VM image:

```bash
bazel build //oak_benchmarks/oak_paper/crypto_channel:crypto_channel_vm
```

1. Start the VM:

```bash
./oak_benchmarks/linux_vm/run_vm.sh \
    --image=bazel-bin/oak_benchmarks/oak_paper/crypto_channel/crypto_channel_vm.qcow2 \
    --port=5000 \
    --port=5001 \
    --port=5002 \
    --headless
```

### Option B: Using `prepare_image.sh` (Manual)

1. Build the server binary and locate the base image:

```bash
bazel build -c opt //oak_benchmarks/oak_paper/crypto_channel:crypto_channel_server
BINARY=$(bazel cquery -c opt //oak_benchmarks/oak_paper/crypto_channel:crypto_channel_server --output=files)
BASE_IMAGE=$(bazel cquery @debian_nocloud_qcow2//file --output=files)
```

1. Prepare the VM image:

```bash
./oak_benchmarks/linux_vm/prepare_image.sh \
    --binary="${BINARY}" \
    --base-image="${BASE_IMAGE}" \
    --output=/tmp/crypto-channel.qcow2 \
    --command="/opt/app/crypto_channel_server --host 0.0.0.0 --plaintext-port 5000 --noise-port 5001 --tls-port 5002"
```

1. Start the VM:

```bash
./oak_benchmarks/linux_vm/run_vm.sh \
    --image=/tmp/crypto-channel.qcow2 \
    --port=5000 \
    --port=5001 \
    --port=5002 \
    --headless
```

### 3. Run the Benchmarks

In another terminal, run the benchmarks:

```bash
bazel run -c opt //oak_benchmarks/oak_paper/crypto_channel:benchmark -- --bench
```

This will run all three protocol benchmarks (plaintext, noise, TLS)
automatically, connecting to the appropriate port for each.

### 4. Stop the VM

Press `Ctrl+C` in the terminal running the VM to stop it (or kill the process if
running with `--headless`).

## Environment Variables

- `VM_HOST`: Host address of the VM (default: `127.0.0.1`)
- `VM_PLAINTEXT_PORT`: Port for plaintext protocol (default: `5000`)
- `VM_NOISE_PORT`: Port for Noise protocol (default: `5001`)
- `VM_TLS_PORT`: Port for the TLS protocol (default: `5002`)
