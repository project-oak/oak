# Roughenough 

[![crates.io](https://img.shields.io/crates/v/roughenough.svg?style=flat-square)](https://crates.io/crates/roughenough)
[![Build Status](https://img.shields.io/travis/int08h/roughenough/master.svg?style=flat-square)](https://travis-ci.org/int08h/roughenough)
[![Apache License 2](https://img.shields.io/badge/license-ASF2-blue.svg?style=flat-square)](https://www.apache.org/licenses/LICENSE-2.0.txt)

**Roughenough** is a [Roughtime](https://roughtime.googlesource.com/roughtime) secure time 
synchronization client and server implementation in Rust. 

Roughenough's server and client are functionally complete and 
at feature parity with the reference C++ and Golang implementations. 

Requires latest stable Rust to compile. Contributions welcome, see
[CONTRIBUTING](../master/CONTRIBUTING.md) for instructions and [limitations](#limitations) for areas that could use attention.

## Links
* [Roughenough Github repo](https://github.com/int08h/roughenough)
* Original [Roughtime project](https://roughtime.googlesource.com/roughtime)
* My blog posts giving a [technical deep-dive into Roughtime](https://int08h.com/post/to-catch-a-lying-timeserver/) and
  exploring details of [on-the-wire Roughtime messages](https://int08h.com/post/roughtime-message-anatomy/).
* Cloudflare's fantastic [blog post](https://blog.cloudflare.com/roughtime/) and accompanying 
  [open-source project](https://developers.cloudflare.com/roughtime/).

## Building and Running

### Rust 1.31 or above required

Roughenough uses [2018 edition](https://rust-lang-nursery.github.io/edition-guide/rust-2018/index.html) 
features and requires Rust 1.31 or newer to build.

### Building

```bash
# Build roughenough
$ cargo build --release
```

The client binary is `target/release/roughenough-client`. After building you can copy the 
binary and run on its own (no `cargo` needed) if you wish.

```bash
$ cp target/release/roughenough-client /usr/local/bin 
```

### Using the Client to Query a Roughtime Server 

```bash
$ target/release/roughenough-client -v roughtime.int08h.com 2002
Requesting time from: "roughtime.int08h.com":2002
Received time from server: midpoint="Oct 26 2018 23:20:44", radius=1000000, verified=No (merkle_index=0)
Oct 26 2018 23:20:44
```

### Setting The System Time on Linux

You can use the `date` utility on Linux machines to set the system time to the time determined by the Roughenough client:

```bash
sudo date --utc --set "$(roughenough-client roughtime.int08h.com 2002)"
```

### Validating Server Responses 

Use the `-p` flag with the client to validate the server's response with its public key.

```bash
# The public key of 'roughtime.int08h.com' is stored in a DNS TXT record 
$ host -t TXT roughtime.int08h.com
roughtime.int08h.com descriptive text "016e6e0284d24c37c6e4d7d8d5b4e1d3c1949ceaa545bf875616c9dce0c9bec1"

# Validate the server response using its public key
$ target/release/roughenough-client -v roughtime.int08h.com 2002 -p 016e6e0284d24c37c6e4d7d8d5b4e1d3c1949ceaa545bf875616c9dce0c9bec1
Requesting time from: "roughtime.int08h.com":2002
Received time from server: midpoint="Oct 26 2018 23:22:20", radius=1000000, verified=Yes (merkle_index=0)
Oct 26 2018 23:22:20
```

The **`verified=Yes`** in the output confirms that the server's response had a valid signature.

### Server Configuration

There are two (mutually exclusive) ways to configure the Roughenough server: 

1. A YAML file, or
2. Environment variables

The server accepts the following configuration parameters:

YAML Key | Environment Variable | Necessity | Description
--- | --- | --- | ---
`interface` | `ROUGHENOUGH_INTERFACE` | Required | IP address or interface name for listening to client requests
`port` | `ROUGHENOUGH_PORT` | Required | UDP port to listen for requests
`seed` | `ROUGHENOUGH_SEED` | Required | A 32-byte hexadecimal value used to generate the server's long-term key pair. **This is a secret value and must be un-guessable**, treat it with care. (If compiled with KMS support, length will vary; see [Optional Features](#optional-features))
`batch_size` | `ROUGHENOUGH_BATCH_SIZE` | Optional | The maximum number of requests to process in one batch. All nonces in a batch are used to build a Merkle tree, the root of which is signed. Default is `64` requests per batch.
`status_interval` | `ROUGHENOUGH_STATUS_INTERVAL` | Optional | Number of _seconds_ between each logged status update. Default is `600` seconds (10 minutes).
`health_check_port` | `ROUGHENOUGH_HEALTH_CHECK_PORT` | Optional | If present, enable an HTTP health check responder on the provided port. **Use with caution**, see [Optional Features](#optional-features).
`kms_protection` | `ROUGHENOUGH_KMS_PROTECTION` | Optional | If compiled with KMS support, the ID of the KMS key used to protect the long-term identity. See [Optional Features](#optional-features).
`fault_percentage` | `ROUGHENOUGH_FAULT_PERCENTAGE` | Optional | Likelihood (as a percentage) that the server will intentionally return an invalid client response. An integer range from `0` (disabled, all responses valid) to `50` (50% of responses will be invalid). Default is `0` (disabled).

#### YAML Configuration 

The table above lists the YAML keys available in the config file. An example:

```yaml
interface: 127.0.0.1
port: 8686
seed: f61075c988feb9cb700a4a6a3291bfbc9cab11b9c9eca8c802468eb38a43d7d3
```

Provide the config file as the single command-line argument to the Roughenough server binary:

```bash
$ /path/to/roughenough-server /path/to/config.yaml
```

#### Environment Configuration

Roughenough can be configured via the `ROUGHENOUGH_*` [environment variables](https://12factor.net/config) 
listed in the table above. Start the server with a single `ENV` argument to have Roughenough configure itself
from the environment. Example:

```bash
$ export ROUGHENOUGH_INTERFACE=127.0.0.1
$ export ROUGHENOUGH_PORT=8686
$ export ROUGHENOUGH_SEED=f61075c988feb9cb700a4a6a3291bfbc9cab11b9c9eca8c802468eb38a43d7d3
$ /path/to/roughenough-server ENV
```

### Starting the Server

```bash
# Build roughenough
$ cargo build --release

# Via a config file
$ target/release/roughenough-server example.cfg
2018-07-25 00:05:09 INFO  [server] Roughenough server v1.0.5 starting
2018-07-25 00:05:09 INFO  [server] Long-term public key: d0756ee69ff5fe96cbcf9273208fec53124b1dd3a24d3910e07c7c54e2473012
2018-07-25 00:05:09 INFO  [server] Ephemeral public key: 25fd5dc31ceee241aed3e643534e95ed0609e9a20982a45ac0312a5f55e2cc66
2018-07-25 00:05:09 INFO  [server] Server listening on 127.0.0.1:8686

# Or using environment variables
$ export ROUGHENOUGH_INTERFACE=127.0.0.1
$ export ROUGHENOUGH_PORT=8686
$ export ROUGHENOUGH_SEED=f61075c988feb9cb700a4a6a3291bfbc9cab11b9c9eca8c802468eb38a43d7d3
$ target/release/roughenough-server ENV
2018-07-25 00:05:09 INFO  [server] Roughenough server v1.0.5 starting
2018-07-25 00:05:09 INFO  [server] Long-term public key: d0756ee69ff5fe96cbcf9273208fec53124b1dd3a24d3910e07c7c54e2473012
2018-07-25 00:05:09 INFO  [server] Ephemeral public key: 25fd5dc31ceee241aed3e643534e95ed0609e9a20982a45ac0312a5f55e2cc66
2018-07-25 00:05:09 INFO  [server] Server listening on 127.0.0.1:8686
```

The resulting binary is `target/release/roughenough-server`. After building you can copy the 
binary and run on its own (no `cargo` needed):

```bash
$ cp target/release/roughenough-server /usr/local/bin 
```

### Stopping the Server

Use Ctrl-C or `kill` the process.


## Optional Features

Roughenough has two opt-in (disabled by default) features that are enabled either 
A) via a config setting, or B) at compile-time.

* [HTTP Health Check responder](doc/OPTIONAL-FEATURES.md#http-health-check) 
  to facilitate detection and replacement of "sick" Roughenough servers.
* [Key Management System (KMS) support](doc/OPTIONAL-FEATURES.md#key-management-system-kms-support)
  to protect the long-term server identity using envelope encryption and 
  AWS or Google KMS.

See [OPTIONAL-FEATURES.md](doc/OPTIONAL-FEATURES.md) for details and instructions
how to enable and use.


## Limitations

Roughtime features not implemented by the server:

* On-line (while server is running) key rotation. The server must be restarted to generate a new delegated key. 
* The Roughenough server depends on the host's time source to comply with the smeared leap-second 
  requirement of the Roughtime protocol. A Roughenough server sourcing time from 
  [Google's public NTP servers](https://developers.google.com/time/) would produce compliant
  smeared leap-seconds but time sourced from members of `pool.ntp.org` likely will not.

## About the Roughtime Protocol
[Roughtime](https://roughtime.googlesource.com/roughtime) is a protocol that aims to achieve rough 
time synchronisation in a secure way that doesn't depend on any particular time server, and in such
a way that, if a time server does misbehave, clients end up with cryptographic proof of it. It was 
created by Adam Langley and Robert Obryk.
  
## Contributors
* Stuart Stock (stuart {at} int08h.com)
* Aaron Hill (aa1ronham {at} gmail.com)
* Peter Todd (pete {at} petertodd.org)
* Muncan90 (github.com/muncan90)
* Zicklag (github.com/zicklag)

## Copyright and License
Roughenough is copyright (c) 2017-2020 int08h LLC. All rights reserved. 

int08h LLC licenses Roughenough (the "Software") to you under the Apache License, version 2.0 
(the "License"); you may not use this Software except in compliance with the License. You may obtain 
a copy of the License from the [LICENSE](../master/LICENSE) file included with the Software or at:

  http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License 
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or 
implied. See the License for the specific language governing permissions and limitations under 
the License.
