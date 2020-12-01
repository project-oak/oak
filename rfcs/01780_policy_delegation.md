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

## Delegation Manifest

The main contribution of this RFC is to specify a mechanism by which parties may
publish a list of hashes in a standard format and serve it statically over
HTTPS.

In the example above, the owner of s_0 would need to publish the signed module
hashes somewhere, and a client would have to know the value of s_0 itself (the
actual key used for signing the module), which introduces extra complexity and
parties around the deployment and publishing of new modules.

Here we introduce a delegation mechanism that is based on the publication of a
manifest file on an HTTPS endpoint.

A Delegation Manifest is identified (and located) by an HTTPS URL pointing to a
JSON file with the schema described below.

For instance, Google may publish a delegation manifest under
`https://google.com/oak/manifests/count_people_from_pixels.json` with the
following contents:

```json
{
  "trusted": [
    {
      "type": "manifest",
      "value": "https://eff.com/oak/manifests/count_people_from_pixels.json"
    },
    {
      "type": "wasm_module",
      "value": "65c296d60c077db03c7ec90c60107a52221c14bb"
    },
    {
      "type": "wasm_module",
      "value": "cf26b96746311908f8fe40340a8b6c1f06f5a1b5"
    }
  ]
}
```

- ~~The `description` field contains a human-readable description of the entries
  that the manifest refers to.~~ This was considered but then removed, so that
  it may not be misused by showing it to users in the wrong context.
- The `trusted` field contains a list of object that are trusted by the
  publisher to conform to the abstract policy identified by the manifest. Each
  object in the `trusted` list is composed of the following fields:
  - `type`: the category of the object (each list of trusted object may have
    objects of various types); some example values of the `type` fields are:
    - `manifest`
    - `wasm_module`
    - `intel_sgx_mrenclave`
  - `value`: a string representing a value that uniquely identifies the trusted
    object; commonly this would be a hash of the object, hex or base64 encoded.

It is possible to include / chain manifests by including the URL of a target
manifest as a trusted object itself, in which case the chain of URLs is
recursively expanded at runtime by Oak.

Note that the manifest does not make any _formal_ guarantees about the inclusion
policy for the objects it refers to; **the meaning of the URL that identifies
the manifest must still be agreed upon informally and out-of-band, and does not
have any inherent meaning to Oak**. A manifest URL may or may not be human
readable at all; in any case it is **not** expected to be displayed to users
directly. ~~The `description` field of the manifest may be used in the context
of displaying to the user, but the link between that and any actual property of
the trusted objects is completely up to the publisher, and based on trusting the
publisher alone.~~

As an example, technically there is nothing stopping Google from (perhaps at
some point in the future) repurposing the manifest identified by
`https://google.com/oak/manifests/count_people_from_pixels.json` to publish
hashes of nodes that count the number of cats instead of the number of people.
The only understanding of what the list of hashes published in a manifest "mean"
is outside of the manifest system itself. It may include formal or informal
guarantees about functionality or policies that the objects are subject to, but
those need to be published separately.

For instance, Google may have a separate web page in which expectations of what
is published in each manifest are detailed, with links to each manifest, and if
relevant perhaps also technical instructions for third parties to independently
verify that such properties are upheld (e.g. source code, training data, etc.).
None of this affects the functioning of the delegation mechanism in Oak though.

## Information Flow Control and Declassification Privilege

Oak is extended with a new principal referring to manifests. When a piece of
data is labelled with the URL of a manifest, Oak treats it as a regular IFC
label.

The Oak Application format is extended to explicitly list the URLs of any
manifests that will be used throughout the execution of the application. The Oak
Runtime fetches those manifests at startup, and recursively denormalizes each
manifest into the corresponding list of Wasm hashes.

When an Oak Application creates a new Wasm Node, the Oak Runtime checks the hash
of the Wasm module to instantiate, and if it correspond to one or more of the
manifests, then it grants the newly created node the corresponding privileges.

For instance, let us assume the following manifests:

- `https://google.com/oak/manifests/count_people_from_pixels.json`:

  ```json
  {
    "trusted": [
      {
        "type": "wasm_module",
        "value": "0000000000000000000000000000000000000000"
      },
      {
        "type": "wasm_module",
        "value": "1111111111111111111111111111111111111111"
      }
    ]
  }
  ```

- `https://apple.com/oak/manifests/count_people_from_pixels.json`:

  ```json
  {
    "trusted": [
      {
        "type": "wasm_module",
        "value": "1111111111111111111111111111111111111111"
      },
      {
        "type": "wasm_module",
        "value": "2222222222222222222222222222222222222222"
      }
    ]
  }
  ```

When an Oak Node with hash `1111111111111111111111111111111111111111` is
instantiated, it receives the declassification privilege of
"manifest:https://google.com/oak/manifests/count_people_from_pixels.json ∧
manifest:https://apple.com/oak/manifests/count_people_from_pixels.json ∧
wasm_hash:1111111111111111111111111111111111111111".

Note that in this case it receives both privileges (or rather, the conjunction
between these privileges), plus the privilege for the corresponding Wasm hash
label, which it would get anyways.

In particular, the conjunctive privilege is quite useful in practice as a
confidentiality label, because it may be used by the data owner to label data
that is expected to be declassified by a Wasm module that is trusted by multiple
parties at the same time, where each party independently publishes a separate
manifest.

## User-based delegation

So far we have talked about companies being the publisher of such manifest, but
it is possible for individual users to also publish manifests for specific use
cases. A user may publish a manifest on a URL hosted on a server they control,
or even as part of another website, e.g. on github.com. Of course, in the case
of publishing on a different website, that website is the ultimate root of trust
of any assertions.

This allows delegation based on existing human-to-human network connections. For
instance, a person may be an expert in a particular field, and independently
verify properties of pieces of software and publish them in a manifest. Also it
is possible for a person publishing a manifest to further delegate to another
publisher (either company or person) by including the URL of the target manifest
as a trusted object in their own manifest.

For instance, a user may publish a manifest at the following URL:
`https://github.com/tiziano88/delegation/count_users_from_pixels.json`, which is
hosted by `github.com`, but of which the user with handle `tiziano88` is
expected to be author:

```json
{
  "trusted": [
    {
      "type": "manifest",
      "value": "https://google.com/oak/manifests/count_people_from_pixels.json"
    },
    {
      "type": "manifest",
      "value": "https://facebook.com/oak/manifests/count_people_from_pixels.json"
    },
    {
      "type": "wasm_module",
      "value": "cf26b96746311908f8fe40340a8b6c1f06f5a1b5"
    }
  ]
}
```

This manifest essentially delegates to the two manifests identified by the URLs
(meaning that the union of the objects trusted by them is trusted by the user),
plus an additional hash that is trusted directly by the user.

## Remote Attestation

Remote attestation is a similar problem to that of trusting Wasm modules with a
given hash. Different parties may have different opinions of what is considered
trustworthy, and those opinions in general change over time.

A company may publish a list of hashes corresponding to remote attestation
quotes of a given system.

For instance, Google may publish a delegation manifest at
`https://google.com/oak/manifests/oak_remote_attestation.json` with the
following contents:

```json
{
  "trusted": [
    {
      "type": "intel_sgx_mrenclave",
      "value": "65c296d60c077db03c7ec90c60107a52221c14bb"
    },
    {
      "type": "intel_sgx_mrenclave",
      "value": "cf26b96746311908f8fe40340a8b6c1f06f5a1b5"
    }
  ]
}
```

This manifest lists the enclave measurements that are expected when connecting
to a legitimate version of the Oak Runtime.

## Revocation

TODO

## Transparency

An issue with the solution as described so far is that it is possible for
publishers to show a different manifest (e.g. including a backdoor) to different
clients (e.g. based on source IP address or time), and they would have no way of
detecting it. To mitigate this, Oak may check for an inclusion proof in a
verifiable log of the specific version of the manfiest, before actually trusting
it. This is left as future work for now.
