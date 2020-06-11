# Information Flow Control (IFC) in Oak

This document describes details of the Information Flow Control system
implemented in Oak.

## Overview

- Nodes and Channels have **Labels**, fixed at creation time
- The Runtime keeps track of Labels, and enforces flow of data between Nodes and
  Channels based on them
- Each Label has two **components**: **confidentiality** and **integrity**
- Each component is an unordered set of **tags**
- Each tag is a structured representation of a **security principal**
- A security principal is either a **user** or a **computation**

## Details

Labels are used to enforce information flow control (IFC) between Nodes and
Channels in an Oak Application and the outside world.

### Runtime

The Oak Runtime keeps track of the Label associated with each Node and each
Channel. When a Node creates a new Node or Channel, the creator Node specifies
the Label to associate with the newly created Node or Channel. The Label does
not change any more after that (apart from explicit declassification operations,
which are not currently supported). Labels are always considered public, and a
Node may inspect its own Label or that of any Channel it has access to, and (if
the Oak Runtime is implemented correctly) this is guaranteed to not allow the
creation of side channels based on Labels.

### Components

A Label has two components: **confidentiality** and **integrity**.

Each component is represented as an (unordered) set of tags, and each tag refers
to an individual security principal in the system.

The following types of security principals are supported in Oak:

- **user**: specified by a bearer token, public key, or some other assertion of
  a user identity
- **computation**: specified by a measurement (hash) of the WebAssembly module
  running within an Oak Node

Tags and Labels are represented as serialized
[protobuf messages](/oak/proto/label.proto).

Any security principal may be used (as a tag) as part of confidentiality or
integrity components, depending on the required use case.

Intuitively, if the confidentiality component contains tag `t`, the Node or
Channel is allowed to see secrets owned by principal `t`. Similarly, if the
integrity component contains tag `t`, that means the Node or Channel is trusted
by `t`.

### Information Flow

Labels are compared to decide whether or not data movement is allowed, for
example when a Node sends a value over a Channel. Given two labels `L_a` and
`L_b`, `L_a ⊑ L_b` (pronounced "flows to") if a value from a source labeled
`L_a` can be sent to a destination labeled `L_b`. The "flows to" operator
compares both confidentiality and integrity:

- the **confidentiality** check ensures that the destination is permitted to
  view any secrets that may have influenced the value
- the **integrity** check ensures that the value sent is trusted by the
  destination

More concretely, if `L_a = (C_a, I_a)` (where `C_a` and `I_a` are the
confidentiality and integrity components respectively), and `L_b = (C_b, I_b)`
then `L_a ⊑ L_b` iff `C_a ⊆ C_b` and `I_a ⊇ I_b`. Notably, the integrity part of
the check is "flipped" by convention (see "Integrity Considerations for Secure
Computer Systems" below). More fundamental than adhering to convention, by
flipping the integrity order in this way, we can retain the intuitive meaning
behind integrity tags as representing trust by a principal (trust by a user,
trust on a subject, etc.).

Intuitively, data can only flow from `a` to `b` if:

- `b` is **at least as secret** as `a`
- `a` is **at least as trusted** as `b`

The least privileged label is usually referred to as "public trusted" (and
represented as `⊥`, pronounced "bottom"), which corresponds to a Node or Channel
which has only observed public data, and its inputs are not endorsed with any
level of integrity; in this label, both confidentiality and integrity components
are empty sets.

As an example, if the `a`'s confidentiality is `{c_0, c_1}`, and `a`'s integrity
is `{i_0, i_1}`, then:

- information can flow from `a` to `b` if `b`'s confidentiality is
  `{c_0, c_1, c_2} ⊇ {c_0, c_1}`, since `b` is "at least as secret" than `a`
- information cannot flow from `a` to `b` if `b`'s confidentiality is
  `{c_0} ⊉ {c_0, c_1}`, since `b` is "less secret" than `a` (in particular, `b`
  is not allowed to see secrets owned by `c_1`)
- information cannot flow from `a` to `b` if `b`'s integrity is
  `{i_0, i_1, i_2} ⊈ {i_0, i_1}`, since `a` is "less trusted" than `b` (in
  particular, `a` is not trusted by `i_2`)
- information can flow from `a` to `b` if `b`'s integrity is
  `{i_0} ⊆ {i_0, i_1}`, since `a` is "at least as trusted" than `b`

In particular:

- A Node with label `L_w` may write to a Channel with Label `L_c` iff
  `L_w ⊑ L_c`.
- A Node with label `L_r` may read from a Channel with Label `L_c` iff
  `L_c ⊑ L_r`.

If a Node tries to write to or read from a Channel that it is not allowed to,
based on the `⊑` relation, the operation fails immediately (i.e. the read or
write ABI call returns an error to the caller), and no side effects are
performed.

It follows that bi-directional communication between Nodes `a` and `b` is only
allowed (via two uni-directional Channels) if
`(L_a ⊑ L_b) ∧ (L_b ⊑ L_a) ⇒ L_a = L_b`, i.e. if `a` and `b` have identical
confidentiality and integrity.

### Downgrades

A Node may have the privilege to remove one or more confidentiality tags
(**declassification**) and / or add one or more integrity tags
(**endorsement**). Both of these operations are instances of **downgrade**
operations (which is a more general concept).

The set of tags that may be downgraded by a Node is determined by the Oak
Runtime based on the initial or current state of the Node. For instance, the Oak
Runtime grants the privilege to declassify user tags to each instance of gRPC
Server Node, which is trusted to only use it in order to declassify data for the
user that is in fact currently authenticated over a gRPC connection.

When Node A attempts to create another Node B, it specifies the desired label
for B, which is checked by the Oak Runtime to be allowed by the "flows to"
relationship, but A does not have a way to influence the privilege of B; this is
always entirely determined by the Oak Runtime itself, which is trusted to assign
the appropriate privilege to all Nodes.

### References

More details on Information Flow Control may be found in the following
references:

- [Information Flow Control for Standard OS Abstractions](https://pdos.csail.mit.edu/papers/flume-sosp07.pdf)
- [Flow-Limited Authorization](https://www.cs.cornell.edu/andru/papers/flam/flam-csf15.pdf)
- [Integrity Considerations for Secure Computer Systems](http://seclab.cs.ucdavis.edu/projects/history/papers/biba75.pdf)
- [Protecting Privacy using the Decentralized Label Model](https://www.cs.cornell.edu/andru/papers/iflow-tosem.pdf)

## gRPC and user labels

As [described elsewhere](/docs/concepts.md#pseudo-nodes), each incoming gRPC
invocation is represented by a message containing two Channels handles:

- a "request receiver" read handle to a Channel whose Label has:

  - a confidentiality component explicitly specified by the caller as gRPC
    request metadata; this represents the confidentiality guarantees that the
    caller wants to impose on the request message.
  - an integrity component implicitly set by the gRPC pseudo-Node based on some
    trusted authentication mechanism that is performed as part of the gRPC
    connection itself; this represents the actual authority of the caller.

- a "response sender" write handle to a Channel, whose Label has:

  - a confidentiality component implicitly set by the gRPC pseudo-Node based on
    some trusted authentication mechanism that is performed as part of the gRPC
    connection itself; this represents the actual authority of the caller.
  - an empty integrity component.
