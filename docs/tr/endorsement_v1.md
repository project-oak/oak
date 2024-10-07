# Endorsement Specification V1

Transparent Release (TR) endorsement statements are represented and serialized
as [JSON] objects.

## Schema

Endorsements are [in-toto statement]s (V1 only) with a custom predicate. In the following
example, only the subject, the timestamps and the claim types are variable.

```jsonc
{
  "_type": "https://in-toto.io/Statement/v1",
  "subject": [
    {
      "name": "oak_orchestrator",
      "digest": {
        "sha256": "8c938394c5962194d1449ee17b4db5fdf5a78729b38ebacf26de9bed4027e351",
      },
    },
  ],
  "predicateType": "https://project-oak.github.io/oak/tr/endorsement/v1",
  "predicate": {
    "issuedOn": "2024-10-07T06:44:22.459000Z",
    "validity": {
      "notBefore": "2024-10-07T06:44:22.459000Z",
      "notAfter": "2025-10-07T06:44:22.459000Z",
    },
    "claims": [
      {
        "type": "https://github.com/project-oak/oak/blob/main/docs/tr/claim/85483.md",
      },
    ],
  },
}
```

## Fields

`_type` _string representing a [TypeURI], required_

> Identifier for the schema of the in-toto statement. Always
> `https://in-toto.io/Statement/v1` for the present endorsements. Only V1
> in-toto statements are supported.

`subject` _array of [ResourceDescriptor] objects, required_

> Fully follows the [in-toto statement] specification.

`predicateType` _string representing a [TypeURI], required_

> Identifies the schema of the predicate. Always
> `https://project-oak.github.io/oak/tr/endorsement/v1` for the present
> endorsements.

The `predicate` includes the following fields:

`predicate.issuedOn` _string representing a [Timestamp], required_

> Specifies when the endorsement was issued.

`predicate.validity.notBefore` _string representing a [Timestamp], required_

> Specifies when the endorsement starts to be valid.

`predicate.validity.notAfter` _string representing a [Timestamp], required_

> Specifies when the endorsement ceases to be valid.

`predicate.claims` _array of claim objects, optional_

> A claim identifies one or more properties the endorser asserts about the
> endorsed subject. Encoded claims have just one `type` field which is a string
> representing a [TypeURI]. The choice of identifier and its meaning are up to
> the endorser.

[JSON]: https://www.json.org/json-en.html
[in-toto statement]: https://in-toto.io/Statement/v1
[ResourceDescriptor]:
  https://github.com/in-toto/attestation/blob/main/spec/v1/resource_descriptor.md
[TypeURI]:
  https://github.com/in-toto/attestation/blob/main/spec/v1/field_types.md#TypeURI
[Timestamp]:
  https://github.com/in-toto/attestation/blob/main/spec/v1/field_types.md#timestamp
