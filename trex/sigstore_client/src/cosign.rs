// Copyright 2025 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use anyhow::Context;
use base64::{prelude::BASE64_STANDARD, Engine};
use oci_client::{secrets::RegistryAuth, Client, Reference};
use sigstore::message::{Raw, SignedMessage, Unverified};

const SIMPLE_SIGNING_MIME_TYPE: &str = "application/vnd.dev.cosign.simplesigning.v1+json";

/// Pulls an arbitrary signed payload from an OCI registry.
/// For details about the storage format see cosign's documentation[^1].
///
/// [^1]: https://github.com/sigstore/cosign/blob/main/specs/SIGNATURE_SPEC.md#storage
pub async fn pull_payload(
    client: &Client,
    auth: &RegistryAuth,
    image: &Reference,
) -> anyhow::Result<(SignedMessage<Unverified>, SignedMessage<Raw>)> {
    // The signature container is in a container in the same registry and repository
    // and can be identified by tag. The tag format is the image's digest with :
    // replaced by -, and with the suffix ".sig".
    let image_sig = match image.digest() {
        Some(digest) => Reference::with_tag(
            image.registry().to_owned(),
            image.repository().to_owned(),
            format!("{}.sig", digest.replace(":", "-")),
        ),
        None => {
            anyhow::bail!("Only digest image references are supported");
        }
    };

    let data = client
        // The cosign tool uses this MIME type for all payloads
        // even if they are not simplesigning-typed.
        // See https://github.com/sigstore/cosign/issues/4300
        .pull(&image_sig, auth, vec![SIMPLE_SIGNING_MIME_TYPE])
        .await?;

    if let Some(layer) = data.layers.into_iter().next() {
        let mut annotations =
            layer.annotations.context("Cosign image does not have layer annotations")?;
        let signature = annotations
            .remove("dev.cosignproject.cosign/signature")
            .context("Cosign image does not have signature annotation")?;
        let signature = BASE64_STANDARD.decode(signature)?;

        let bundle = annotations
            .remove("dev.sigstore.cosign/bundle")
            .context("Cosign image does not have bundle annotation")?;

        Ok((SignedMessage::unverified(layer.data, signature), SignedMessage::raw(bundle.into())))
    } else {
        anyhow::bail!("No layers found in image");
    }
}
