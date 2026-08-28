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

The Noise legs are **unattested** NoiseNN (`AttestationType::Unattested`).
Nothing here exercises attestation, so no number produced by this crate says
anything about DICE or attestation verification cost.

All measurements are taken on the host side.

- In general, we are interested in relative latencies rather than absolute
  latencies, so consistency between the test types is important.
- In tests that measure sending speeds, a short ACK from the server is used to
  indicate complete reception of the data.
- In tests that measure receive speeds, the host measures the time it takes to
  receive the expected amount of data.

## What each group measures

Every leg reports two groups.

| Group suffix           | Timed region                                |
| ---------------------- | ------------------------------------------- |
| `... Message Exchange` | one send and one receive on an open channel |
| `... Setup`            | transport connect plus the leg's handshake  |

`Message Exchange` reports `(send + recv) / 2`, a **mean one-way latency, not a
round trip**. Do not quote it as an RTT.

`Setup` is the metric the evaluation plan calls handshake latency. The plaintext
leg has no handshake, so its `Setup` figure is the transport cost alone and is
the floor the other legs should be read against.

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
out. It is **not** the listen backlog -- the kernel completes a loopback connect
without the server calling `accept`. And it is **not** ephemeral-port or
`TIME_WAIT` pressure -- sweeping `TIME_WAIT` occupancy from 36 to 87,084 sockets
moves the figure by 0.7%, and the faster runs hold _more_ sockets in `TIME_WAIT`
than the slower ones.

25 µs is about one loopback round trip on the host this was measured on, which
is suggestive but **not** established as a scaling law: the threshold was only
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
duty cycle depressing the boost clock, and points instead at the _server_ thread
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
> stays wide, so narrowing is good confirmation. The converse does **not** hold:
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
unacknowledged segment ever precedes the write. rustls suffered less because it
coalesces a record into one write rather than two. Noise took the full stall on
every message.

> [!NOTE] The `Setup` rows above predate `SETUP_SETTLE`. Both columns were
> measured without the settle interval, so the comparison between them is sound,
> but the absolute plaintext `Setup` figure is roughly double what the current
> harness reports. It is now about 16.4 us rather than 33.77 us.

Read against the corrected figures, the Noise data path costs 4% over plaintext
and beats rustls by 1.4x on the message-exchange arm. Both halves are worth
knowing and neither was visible before.

> [!WARNING] This section used to add "while Noise setup is 3.1x _slower_ than a
> rustls handshake". **That was wrong.** The rustls leg was resuming its TLS
> sessions -- one `ClientConfig` was shared across every iteration and
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
