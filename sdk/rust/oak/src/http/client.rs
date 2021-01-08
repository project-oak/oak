//
// Copyright 2020 The Project Oak Authors
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
//

use crate::{http::HttpInvocation, OakStatus};
use oak_abi::label::{confidentiality_label, tls_endpoint_tag, Label};
use oak_io::Sender;

/// Initializes an HTTP client pseudo-Node serving requests that have the given authority in their
/// URIs. If the authority is empty, the node is public and can handle any incoming request.
/// Otherwise, the node is created with the `authority` as its confidentially tag. In this case, the
/// client can only serve HTTPS requests to the services indicated by the `authority`.
pub fn init(authority: &str) -> Result<Sender<HttpInvocation>, OakStatus> {
    let config = crate::node_config::http_client(authority);
    let label = if authority.is_empty() {
        Label::public_untrusted()
    } else {
        confidentiality_label(tls_endpoint_tag(authority))
    };
    crate::io::node_create::<HttpInvocation>("http_client", &label, &config)
}
