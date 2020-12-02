# Policy Delegation

The main way of expressing policies in Oak is to attach a label to each piece of
data flowing through the system, usually as gRPC metadata or HTTP headers
attached to an incoming request as it enters an Oak Application.

The confidentiality component of a label determines how data can flow and be
declassified through the application. This means that it is fixed at ingestion
time, and cannot be changed subsequently.

This RFC proposes a more practical and scalable way of representing and
enforcing delegation of policies (mainly for declassification purposes).

## Background

In this section we describe the currently available mechanisms for
declassification and labelling. Readers familiar with these aspects may skip to
the [`Delegation Manifest`](#delegation-manifest) section.

### Wasm Module Hash

https://github.com/project-oak/oak/blob/573e61e74668db3eb53747f38757b00aa899f1f6/oak_abi/proto/label.proto#L62-L69

This principal refers to a specific Wasm module, identified by a particular
hash. In order for this principal to be meaningfully used by end users, it would
require them to somehow gain trust in the code that the hash refers to. This is
usually accomplished by reviewing the source code from which the module was
compiled, by informally or formally ensuring that it matches the user's
expectations in terms of declassification abilities, and then independently
compiling it to Wasm in a reproducible way, producing an artefact identical to
the one that is being verified to which the hash refers.

Admittedly all of this is unlikely to be performed by regular (or even advanced)
users. Also, it would be unlikely to be useful in practice, because code often
evolves, and therefore previous data labelled with a specific Wasm module hash
label would not be able to be declassified by new versions of the code, whatever
that means in practice (e.g. a version with bug fixes or improved
functionality).

### Wasm Module Signature

https://github.com/project-oak/oak/blob/573e61e74668db3eb53747f38757b00aa899f1f6/oak_abi/proto/label.proto#L71-L77

In order to facilitate more useful data flows with declassification other than
just individual Wasm modules identified by a precise hash, Oak also supports
Wasm module signature labels.

A Wasm module signature principal refers to a public key that is used to sign
any number of individual Wasm modules (or more precisely, to sign their hashes).

For instance, let's assume there are three Wasm modules, with hashes
respectively w_0, w_1, w_2. Also there are two (public, secret) key pairs (p_0,
s_0), (p_1, s_1).

Let's assume that the modules are supposed to implement some declassification
logic, e.g. counting the number of people in an image given raw pixels. s_0 and
s_1 are two parties that verify such models (from correctness, privacy and
security point of view) and sign them if they (respectively) believe that they
are trustworthy.

The owner of s_0 signs w_0 and w_1 with s_0, while the owner of s_1 signs w_1
and w_2 with s_1:

```text
    ┌ w_0
s_0 │
    └ w_1 ┐
          │ s_1
      w_2 ┘
```

## Discovery Manifest

The main contribution of this RFC is to specify a mechanism by which parties may
publish and discover lists of links to signed module hashes over HTTP(S).

In the example above, the owner of s_0 would need to publish the signed module
hashes somewhere, and a client would have to know where to find them, which is
not currently specified and introduces extra complexity and parties around the
deployment and publishing of new modules.

A Discovery Manifest is identified (and located) by an HTTP(S) URL pointing to a
JSON file containing lists of URLs (relative or absolute) from which to fetch
signed Wasm module hashes, or other manifests. Relative URLs are resolved taking
as
[base](https://docs.rs/url/2.2.0/url/struct.ParseOptions.html#method.base_url)
URL the URL of the manifest file itself.

- the `includes` field lists URLs of other Discovery Manifests (of the same
  format) to include / chain. Manifests linked this way are recursively expanded
  by the Oak Runtime, taking care of avoiding cycles, and also possibly with a
  bounded recursion limit which is configurable in the Oak Runtime (e.g. max 256
  hops).
- the `signatures` field lists URLs of signed module hashes to load, in the
  format already used in Oak for this purpose (e.g.
  [private_set_intersection_handler.sign](https://github.com/project-oak/oak/blob/main/examples/private_set_intersection/private_set_intersection_handler.sign)).

For instance, Google may publish a discovery manifest under
`https://google.com/oak/manifests/count_people_from_pixels.links` (the exact
URL, name and extension of the document are irrelevant) with the following
contents:

```json
{
  "includes": ["https://other-company.com/oak/manifests/index.links"],
  "signatures": [
    "./count_people_from_pixels_v0.sign",
    "./count_people_from_pixels_v1.sign"
  ]
}
```

Then `https://google.com/oak/manifests/count_people_from_pixels_v0.sign`
(resolved as a relative URL) may contain an actual signed module hash:

```text
-----BEGIN PUBLIC KEY-----
f41SClNtR4i46v2Tuh1fQLbt/ZqRr1lENajCW92jyP4=
-----END PUBLIC KEY-----

-----BEGIN SIGNATURE-----
DvtzJOF5nfOIyalYPtZxAr3cYnQrNKbmapNv+ZiFOkheKtKbar26M69vPMQwGCAa
WC9QIdhLXyhY/kRDzUX9Dg==
-----END SIGNATURE-----

-----BEGIN HASH-----
xCIVq3nTGs945zaWcnVTF02EHyFjc9yJCkr6m2X+uO0=
-----END HASH-----
```

The URLs in a Discovery Manifest do not need to all point to signed module
hashes from the same key. In fact, the manifest itself is just a way of
discovering the actual signed module hashes, which are themselves
cryptographically self-contained; **a Discovery Manifest is not an endorsement
of any included Discovery Manifests or signed module hashes in any way**. Trust
in individual signed module hashes is only based on the actual signature they
contain and the link to the corresponding public key.

For instance, an attacker with control of a Discovery Manifest (but no signing
keys) would not be able to compromise the security of the delegation process
(though it may cause a Denial of Service):

- removing a link to a manifest or to a signature would just cause that
  signature or manifest to not be considered when computing the privilege of
  Wasm nodes, therefore making information flow more constrained
- adding a link to an additional signature file would cause the signature to be
  included in the computation of the privilege of Wasm nodes, but unless the key
  is already trusted by any client, the new privilege would be useless
- adding a link to an additional Discovery Manifest would just let that manifest
  expand recursively

Incidentally, this also means that, strictly speaking, it is not _necessary_ for
manifests to be served over HTTPS.

It is not possible (within the scope of this RFC) for a key to sign another key.
If the owner of private key s_1 wants to express complete delegation to the
owner of key s_0, the owner of s_1 would have to fetch all signed module hashes
signed by s_0, re-sign them with s_1, and publish them as separate signed module
hashes. This may be automated or facilitate via some tooling, but it is still an
operation that must happen for each module hash that is delegated.

This still leaves open the problem of discovering and trusting public keys,
especially from the point of view of a client. In the absence of other PKIs
(e.g. keybase.io, key transparency), we will rely on the public keys being
published over TLS or some other mechanism, which is out of scope for this RFC.

Note that the expectation is that each entity would create a separate key pair
for each purpose for which they will sign module hashes. For instance,
google.com would create (and publicize) a key to sign Wasm modules counting
number of people, and then a separate, independent key to sign Wasm modules
counting number of cats. These keys would not be related to each other, apart
from perhaps being both discoverable from some web page served by google.com.

Developers of client applications would find the keys for the set of modules
that they expect to delegate trust to, and pin the key in the client code
(similar to
[TLS certificate pinning](https://www.digicert.com/blog/certificate-pinning-what-is-certificate-pinning/)).

Longer-term, a set of keys may be included in a device, similarly to how root
CAs are preinstalled on most devices, or a multi-layer signing scheme may be
used to delegate keys to other keys, but this is out of scope for this RFC.

Note that a key pair by itself does not make any _formal_ guarantees about the
inclusion policy for the objects it signs; **the semantics of signing a module
with a particular key must still be agreed upon informally and out-of-band, and
does not have any inherent meaning to Oak**.

As an example, technically there is nothing stopping Google from (perhaps at
some point in the future) repurposing the private counterpart of the public key
identified by `https://google.com/oak/keys/count_people_from_pixels.pub` to sign
hashes of modules that count the number of cats instead of the number of people.
The only understanding of what the hashes signed with a given particular key
"mean" is outside of the key signing system itself. The owner of the private key
may make formal or informal guarantees about functionality or policies related
to the trusted objects, but those need to be published separately.

For instance, Google may have a separate web page in which expectations of what
is signed with each private key are detailed, with links to corresponding public
key, and, if relevant, perhaps also technical instructions for third parties to
independently verify that such properties are upheld (e.g. source code, training
data, etc.). None of this affects the functioning of the delegation mechanism in
Oak though.

## Information Flow Control and Declassification Privilege

Oak is extended with a new principal referring to manifests. When a piece of
data is labelled with the URL of a manifest, Oak treats it as a regular IFC
label.

The Oak Runtime is extended to accept a list of URLs of initial Discovery
Manifests which it recursively expands (up to a configurable recursion limit,
and avoiding cycles) at startup, creating a local cache mapping each public key
to the list of modules signed with it, and each module to the list of keys that
signed it.

When an Oak Application creates a new Wasm Node, the Oak Runtime checks the hash
of the Wasm module to instantiate, and if it corresponds to one or more valid
signed module hashes, then it grants the newly created node the privilege
corresponding to their respective public keys.

For instance, let us assume the following configuration:

- `https://google.com/oak/keys/count_people_from_pixels.pub`:

  - contents:

    ```text
    -----BEGIN PUBLIC KEY-----
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
    -----END PUBLIC KEY-----
    ```

  - used to sign modules with the following hashes:
    - `0000000000000000000000000000000000000000`
    - `1111111111111111111111111111111111111111`

- `https://other-company.com/oak/keys/count_people_from_pixels.pub`:

  - contents:

    ```text
    -----BEGIN PUBLIC KEY-----
    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
    -----END PUBLIC KEY-----
    ```

  - used to sign modules with the following hashes:
    - `1111111111111111111111111111111111111111`
    - `2222222222222222222222222222222222222222`

When an Oak Node with hash `1111111111111111111111111111111111111111` is
instantiated, it receives the declassification privilege of
"signature:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa ∧
signature:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb ∧
wasm_hash:1111111111111111111111111111111111111111".

Note that in this case it receives both privileges (or rather, the conjunction
between these privileges), plus the privilege for the corresponding Wasm hash
label, which it would get anyways even in the absence of any signed module hash
referring to it.

In particular, the conjunctive privilege is quite useful in practice as a
confidentiality label, because it may be used by the data owner to label data
that is expected to be declassified by a Wasm module that is trusted by multiple
parties at the same time, where each party independently publishes a separate
manifest.

## User-based delegation

So far we have talked about companies being the publisher of such manifest, but
it is possible for individual users to also publish signed module hashes for
specific use cases. A user may publish a list of signed module hashes on a
website that they control, or even as part of another website, e.g. on
github.com. They also need to publish their public key, in a way that allows
other users to reliably find it and use it as part of an Oak application.

This allows delegation based on existing human-to-human network connections. For
instance, a person may be an expert in a particular field, and independently
verify properties of pieces of software and publish them as signed module hashes
with a particular key, which they would also publish. Also it is possible for a
person publishing a public key to further delegate to another public key (either
company or person) by re-signing all the signed module hashes already signed by
the other key.

For instance, a user may publish a manifest and corresponding signatures at the
following URL:
`https://github.com/tiziano88/delegation/count_users_from_pixels.links`:

```json
{
  "includes": [],
  "signatures": [
    "./count_people_from_pixels_google.sign",
    "./count_people_from_pixels_other_company.sign"
  ]
}
```

The module hashes were originally published by google and other-company, but in
this case they would be re-signed by the user's key.

## Remote Attestation

Remote attestation is a similar problem to that of trusting Wasm modules with a
given hash. Different parties may have different opinions of what is considered
trustworthy, and those opinions in general change over time.

A company may publish a list of hashes corresponding to remote attestation
quotes of a given system.

For instance, Google may publish a signed module hash that refers to a binary
enclave file (instead of a Wasm module), including the enclave measurements that
is expected when connecting to a legitimate version of the Oak Runtime.

## Revocation

TODO

## Transparency

An issue with the solution as described so far is that it is possible for
publishers to show a different set of signatures (e.g. including a backdoor) to
different clients (e.g. based on source IP address or time), and clients would
have no way of detecting it. To mitigate this, Oak may check for an inclusion
proof in a verifiable log of the specific version of the signatures, before
actually trusting it. This is left as future work.
