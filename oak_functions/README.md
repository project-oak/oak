# Oak Functions

Oak Functions is a stripped-down version of Oak, and is particularly designed
for implementing stateless applications. The objective of Oak Functions is to
design and implement a general-purpose computing platform that allows computing
and storage in a privacy preserving way, leverages TEEs and remote attestation,
Wasm sandboxing, and allows exposing metrics in a Differentially Private way.

We use the same main building blocks used in Oak:

- A Trusted Execution Environment (TEE)
  - This protects the data from the Host, other enclaves and processes, and even
    some HW attacks
  - TEEs can be VM-based (e.g., AMD SEV) or HW-backed (e.g., Intel SGX). Either
    variant can be used for hosting an Oak Functions application.
- Sandboxing the workload, currently using WebAssembly
  - The TEE protects from the host, and anything malicious on it, but to prevent
    malicious behavior in the code itself we need to sandbox the code and limit
    its privileges.
- Remote Attestation
  - So that the client can ensure that it is interacting with a legitimate and
    trustworthy Oak Function loader.

The following diagram shows how the computation model of Oak Functions (and Oak)
differs from the conventional computation model.

<!-- From: -->
<!-- https://docs.google.com/drawings/d/1ZPeJ93IkyOOJVI8CFSbEeEKn6wVozB-d6E1SekK2QyQ/edit -->
<img src="images/ComputingModel.png" width="1000">

## Comparison with Oak

Oak Functions has borrowed many ideas from Oak, but is different from it in a
few ways that are described in this section.

### Number of Wasm modules

While an Oak application may have more than one Wasm module, each Oak Functions
application can only have one Wasm module. The Oak Functions loader instantiates
this single Wasm module for each incoming user request, runs the request through
it in order to produce a response, and then terminates the Wasm instance; each
Wasm instance is short lived and stateless.

Structurally, an Oak Functions application is very similar to a single-node Oak
application. This simplifies the design considerably. Since there is only one
Oak node (i.e., Wasm module), and the native APIs are no longer implemented as
pseudo-nodes, there is no need for message passing over channels. As a
consequence, we no longer require information flow control (IFC) to police the
flow of data from one node to another. The developers do not have to deal with
IFC labels or more advanced concepts and patterns.

Similar to Oak, we have implemented several layers of defense in depth. In
particular, application owners can control which functionalities to enable in a
server configuration file.

As part of our shift to a distributed runtime, in the future, we may allow
native Oak Functions modules that do not run any untrusted Wasm code. An example
is a native Oak Functions module for collecting differentially private metrics,
deployed on its own TEE instances.

### Policies

The server configuration specifies a policy with fields for various
privacy-related parameters. Currently these parameters specify a fixed size for
responses returned by the trusted runtime, and a fixed processing time. The
policy is used to avoid side channel leaks (e.g., an outside attacker observing
the processing time of a request). The Oak Functions loader guarantees that
processing every request takes approximately the specified amount of time and
results in a response of exactly the specified size. If processing an incoming
request completes before the specified time in the policy, the response will not
be sent back until the time is elapsed. On the other hand, if processing the
request does not finish within this deadline, the Oak Functions loader
terminates the process early and responds with an error. Note that we can only
guarantee an approximation of the specified processing time, because the actual
processing time is affected by factors beyond the specific Wasm logic invoked by
the incoming request. These factors include the general server’s state, and how
busy it is overall. Therefore the variation in the actual processing time is in
fact random noise and cannot be used to leak information about the request via
the specific Wasm logic it invoked.

The configuration may in addition specify parameters related to differentially
private metrics, if that feature is enabled. These parameters include a list of
events, a batch size and an epsilon parameter for computing a Laplacian noise.
If metrics are enabled, the trusted runtime collects event counts for events
specified in the configuration, and aggregates them after the batch size is
reached. A laplacian noise, calculated using the specified epsilon parameter, is
then added to the aggregated value, to conform to the differential privacy
requirements, before publishing the results by logging to stdout.

### No external interaction and read-only storage

An Oak application can have restricted interactions with the external world via
gRPC and HTTP pseudo-nodes. There is no equivalent functionality in an Oak
Functions application. However, an Oak Functions can have a read-only storage
that is populated with data from an external data source. The external resource
has to be specified in the server configuration file. It is also possible to
specify a refresh interval. This allows the Oak Functions loader to periodically
refresh the data in the storage, by re-downloading the entirety of the data from
a URL provided in the server configuration file.

The storage is implemented as an in-memory key-value store (in practice a
hashmap), of which there is one instance per Oak Functions loader instance,
which is shared across invocations of the Wasm logic. The property that this
offers is that queries are not observable (and not logged) by the loader, since
they happen within the same process, which eventually is going to be contained
in a single TEE instance. Oak Functions provides a
[lookup API](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#storage_get_item)
as part of the SDK that the Wasm modules can use to fetch data from the storage.

### Remote attestation

The Remote Attestation protocol implemented in Oak is currently integrated in
Oak Functions.

## Applications

The assumption is that Oak Functions only covers a subset of the use cases
compared to Oak, but those use cases are the most commonly occurring ones. One
apparent restriction is the use of a read-only in-memory storage. With a
distributed runtime however, it should be possible to use Oak Functions for
applications that require larger storage.

We have an experimental support for ML-inference using TensorFlow models in Oak
Functions. The benefit of this, compared to running ML-inference on-device, is
that the model will remain protected and secure.
