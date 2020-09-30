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

use crate::proto::oak::encap::{HeaderMap, HeaderValue, HttpRequest, HttpResponse};
use http::{Request, Response};
use log::warn;
use maplit::hashmap;
use oak_abi::OakStatus;

impl From<&Response<Vec<u8>>> for HttpResponse {
    fn from(response: &Response<Vec<u8>>) -> Self {
        HttpResponse {
            body: response.body().to_owned(),
            status: response.status().as_u16() as i32,
            headers: Some(HeaderMap::from(response.headers().to_owned())),
        }
    }
}

impl std::convert::TryFrom<HttpRequest> for Request<Vec<u8>> {
    type Error = OakStatus;
    fn try_from(request: HttpRequest) -> Result<Self, Self::Error> {
        let mut builder = Request::builder()
            .method(request.method.as_bytes())
            .uri(request.uri);
        if let Some(headers) = request.headers {
            for (header_name, header_value) in headers.iter() {
                builder = builder.header(header_name, header_value);
            }
        }
        builder.body(request.body).map_err(|err| {
            warn!("Could not create request: {}", err);
            OakStatus::ErrInternal
        })
    }
}

impl From<http::header::HeaderMap<http::header::HeaderValue>> for HeaderMap {
    fn from(http_headers: http::header::HeaderMap<http::header::HeaderValue>) -> Self {
        let mut headers = hashmap! {};
        for (header_name, header_value) in &http_headers {
            headers
                .entry(header_name.to_string())
                .or_insert_with(Vec::new)
                .push(header_value.as_bytes().to_vec())
        }
        let headers = headers
            .iter()
            .map(|(name, value)| {
                (
                    name.to_owned(),
                    HeaderValue {
                        values: value.to_owned(),
                    },
                )
            })
            .collect();

        HeaderMap { headers }
    }
}

impl HeaderMap {
    /// Flatten the headers into an iterator of tuples (String, http::header::HeaderValue).
    pub fn iter(
        &self,
    ) -> impl Iterator<Item = (http::header::HeaderName, http::header::HeaderValue)> + '_ {
        self.headers
            .iter()
            .flat_map(|(name, value)| {
                value.values.iter().filter_map(move |val| {
                    let name_value_pair = || -> Result<(http::header::HeaderName, http::header::HeaderValue), OakStatus>  {
                        let header_name = http::header::HeaderName::from_bytes(name.as_bytes())
                            .map_err(|err| {
                                warn!("Error when parsing header name: {}", err);
                                OakStatus::ErrInternal
                            })?;
                        let header_value =
                            http::header::HeaderValue::from_bytes(val).map_err(|err| {
                                warn!("Error when parsing header value: {}", err);
                                OakStatus::ErrInternal
                            })?;
                        Ok((header_name, header_value))
                    };
                    name_value_pair().ok()
                })
            })
    }
}
