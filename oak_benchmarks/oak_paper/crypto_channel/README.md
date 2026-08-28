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

A fresh channel is created for every iteration of `Message Exchange`, so the
comparison is currently **handshake-per-RPC only**. The single-long-lived-
channel arm is not implemented: `linux_server::start_tcp_server` serves exactly
one message per connection, so measuring channel reuse needs a server that loops
on the connection, and that needs `MessageStream` to be able to report
end-of-stream instead of panicking.

> [!IMPORTANT] Until 2026-08 the TLS leg's handshake was charged to its first
> timed send. `rustls::StreamOwned::new` does not handshake; rustls defers it to
> first use, and nothing forced it earlier. The Noise leg, whose handshake
> happens eagerly in `NoiseMessageStream::new_client`, was not charged for its
> own. The legs were not measuring the same thing. `new_tls_client_stream` now
> calls `complete_io` so the handshake lands in `Setup` on every leg. Removing
> it from the timed send cut the reported TLS exchange latency by about half.

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
