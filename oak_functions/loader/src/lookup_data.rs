//
// Copyright 2021 The Project Oak Authors
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

use crate::logger::Logger;
use anyhow::{anyhow, Context};
use hyper::{body::Bytes, client::connect::Connect, Body, Client, Request};
use hyper_rustls::HttpsConnectorBuilder;
use log::Level;
use oak_logger::OakLogger;
use prost::Message;
use serde_derive::Deserialize;
use std::{collections::HashMap, sync::RwLock, time::Instant};

#[derive(Copy, Clone, Deserialize, Debug)]
pub enum LookupDataAuth {
    None,
    GcpMetadataToken,
}

impl LookupDataAuth {
    pub fn default() -> Self {
        LookupDataAuth::None
    }
}

#[derive(Clone, Debug)]
pub enum LookupDataSource {
    Http { url: String, auth: LookupDataAuth },
    File(std::path::PathBuf),
}

/// An in-memory lookup store instance that can refresh its internal entries from the provided data
/// file URL.
///
/// Entries in the data file path must be consecutive binary encoded and length delimited
/// protobuf messages according to the definition in `/oak_functions/proto/lookup_data.proto`.
pub struct LookupData {
    lookup_data_source: Option<LookupDataSource>,
    entries: RwLock<HashMap<Vec<u8>, Vec<u8>>>,
    logger: Logger,
}

impl LookupData {
    /// Creates a new empty [`LookupData`] instance that can refresh its internal entries from the
    /// provided data file URL.
    ///
    /// The returned instance is empty, and must be populated by calling the [`LookupData::refresh`]
    /// method at least once.
    pub fn new_empty(lookup_data_source: Option<LookupDataSource>, logger: Logger) -> LookupData {
        LookupData {
            lookup_data_source,
            entries: RwLock::new(HashMap::new()),
            logger,
        }
    }

    /// Refreshes the internal entries of this struct from the data file URL provided at
    /// construction time.
    ///
    /// If the `lookup_data_auth` config setting is set to `GcpMetadataToken` a service account
    /// access token token will be downloaded from the GCP metadata service first and then used to
    /// authenticate the lookup data download request.
    ///
    /// If successful, entries are completely replaced (i.e. not merged).
    ///
    /// If there is any error while reading or parsing the data, an error is returned by this
    /// method, and existing entries are left untouched. The caller may retry the refresh operation
    /// at a future time.
    pub async fn refresh(&self) -> anyhow::Result<()> {
        match &self.lookup_data_source {
            Some(lookup_data_source) => {
                let start = Instant::now();
                let lookup_data_buf = fetch_lookup_data(&self.logger, lookup_data_source).await?;
                self.logger.log_public(
                    Level::Info,
                    &format!(
                        "fetched {} bytes of lookup data in {:.0?}",
                        lookup_data_buf.len(),
                        start.elapsed()
                    ),
                );

                let start = Instant::now();
                let entries = parse_lookup_entries(&mut lookup_data_buf.as_ref())
                    .context("could not parse lookup data")?;

                self.logger.log_public(
                    Level::Info,
                    &format!(
                        "parsed {} entries of lookup data in {:.0?}",
                        entries.len(),
                        start.elapsed()
                    ),
                );

                // This block is here to emphasize and ensure that the write lock is only held for a
                // very short time.
                let start = Instant::now();
                {
                    *self
                        .entries
                        .write()
                        .expect("could not lock entries for write") = entries;
                }
                self.logger.log_public(
                    Level::Debug,
                    &format!(
                        "lookup data write lock acquisition time: {:.0?}",
                        start.elapsed()
                    ),
                );

                Ok(())
            }
            None => Ok(()),
        }
    }

    /// Creates an instance of LookupData populated with the given entries.
    #[allow(dead_code)]
    pub fn for_test(entries: HashMap<Vec<u8>, Vec<u8>>) -> Self {
        LookupData {
            lookup_data_source: None,
            entries: RwLock::new(entries),
            logger: Logger::for_test(),
        }
    }

    /// Convenience getter for an individual entry that reduces lock contention by cloning the
    /// resulting value as quickly as possible and returning it instead of a reference.
    pub fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        self.entries
            .read()
            .expect("could not lock entries for read")
            .get(key)
            .cloned()
    }

    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.entries
            .read()
            .expect("could not lock entries for read")
            .len()
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.entries
            .read()
            .expect("Could not lock entries for read")
            .is_empty()
    }
}

async fn fetch_lookup_data(
    logger: &Logger,
    lookup_data_source: &LookupDataSource,
) -> anyhow::Result<Bytes> {
    match lookup_data_source {
        LookupDataSource::Http { url, auth } => {
            logger.log_public(
                Level::Info,
                &format!(
                    "refreshing lookup data from HTTP: {} with auth {:?}",
                    url, auth
                ),
            );
            // TODO(#1930): Avoid loading the entire file in memory for parsing.
            let https = HttpsConnectorBuilder::new()
                .with_native_roots()
                .https_or_http()
                .enable_http1()
                .build();
            let client = Client::builder().build::<_, Body>(https);
            send_request(&client, build_download_request(url, auth).await?).await
        }
        LookupDataSource::File(file_path) => {
            logger.log_public(
                Level::Info,
                &format!("refreshing lookup data from file path: {:?}", file_path),
            );
            Ok(tokio::fs::read(&file_path).await?.into())
        }
    }
}

pub fn parse_lookup_entries<B: prost::bytes::Buf>(
    lookup_data_buffer: B,
) -> anyhow::Result<HashMap<Vec<u8>, Vec<u8>>> {
    let mut lookup_data_buffer = lookup_data_buffer;
    let mut entries = HashMap::new();
    while lookup_data_buffer.has_remaining() {
        let entry =
            oak_functions_abi::proto::Entry::decode_length_delimited(&mut lookup_data_buffer)
                .context("could not decode entry")?;
        entries.insert(entry.key, entry.value);
    }
    Ok(entries)
}

async fn build_download_request(url: &str, auth: &LookupDataAuth) -> anyhow::Result<Request<Body>> {
    let builder = match auth {
        LookupDataAuth::None => Request::builder().method(http::Method::GET).uri(url),
        LookupDataAuth::GcpMetadataToken => {
            let access_token = get_access_token()
                .await
                .context("could not get access token")?;
            Request::builder()
                .method(http::Method::GET)
                .uri(url)
                .header("Authorization", format!("Bearer {}", access_token))
        }
    };
    builder
        .body(Body::empty())
        .context("could not create lookup data request")
}

async fn send_request<C>(client: &Client<C, Body>, request: Request<Body>) -> anyhow::Result<Bytes>
where
    C: Connect + Clone + Send + Sync + 'static,
{
    let response = client
        .request(request)
        .await
        .context("could not execute request")?;
    hyper::body::to_bytes(response.into_body())
        .await
        .context("could not read response body")
}

/// Gets a service account access token from the GCP metadata service.
async fn get_access_token() -> anyhow::Result<String> {
    let client = Client::new();
    let request = Request::builder()
        .method(http::Method::GET)
        // See https://cloud.google.com/run/docs/securing/service-identity#access_tokens for details.
        .uri("http://metadata.google.internal/computeMetadata/v1/instance/service-accounts/default/token")
        .header("Metadata-Flavor", "Google")
        .body(Body::empty())
        .context("could not create auth token request")?;
    let result = send_request(&client, request).await?;
    let token_json =
        std::str::from_utf8(result.as_ref()).context("could not decode response as a string")?;
    let token: serde_json::Value =
        serde_json::from_str(token_json).context("could not decode response as JSON")?;
    token["access_token"]
        .as_str()
        .ok_or_else(|| anyhow!("access token not found"))
        .map(String::from)
}
