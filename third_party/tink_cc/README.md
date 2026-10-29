# tink-cc patches

[tink-cc](https://github.com/tink-crypto/tink-cc) is fetched from the
[Bazel Central Registry](https://registry.bazel.build/modules/tink_cc) as a
Bazel module dependency (`@tink_cc`, with repo name
`@com_github_tink_crypto_tink_cc`). `MODULE.bazel` applies the patches in
`patches/` with a `single_version_override`.

Patches:

- `01_ecdsa_parameters_visibility.patch`: makes
  `//tink/signature:ecdsa_parameters` visible outside the tink-cc module.

In tink-cc 2.7.0, `EcdsaParameters` (and
`KeysetHandle::GenerateNewFromParameters`) are part of the public C++ API, but
the `ecdsa_parameters` Bazel target is restricted to tink-cc itself by the
package `default_visibility`
([BUILD.bazel](https://github.com/tink-crypto/tink-cc/blob/v2.7.0/tink/signature/BUILD.bazel)).
The patch lets Oak generate ECDSA keys from parameters (see
`cc/crypto/tink/signature/ecdsa_p256_parameters.h`) instead of the deprecated
`SignatureKeyTemplates`, which are scheduled for removal in tink-cc 3.0.

TODO: b/573931130 - Remove the override and this directory once Oak moves to
tink-cc 3.0, where the target is public upstream
([main](https://github.com/tink-crypto/tink-cc/blob/main/tink/signature/BUILD.bazel)).
