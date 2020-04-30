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

use bytes::buf::BufExt as _;
use http::{Request, Uri};
use hyper::{
    body::{aggregate, Body},
    Client, StatusCode,
};
use hyper_tls::HttpsConnector;
use log::info;
use std::{error, fmt, io::copy};

/// Performs an HTTP GET operation to the specified URI.
// TODO(#924): Support caching based on the max-age value of the cache-control response header
pub async fn get(uri: Uri) -> Result<String, Box<dyn error::Error>> {
    info!("Geting {}", &uri);
    execute_request(Request::get(uri).body(Body::from(""))?).await
}

/// Performs an HTTP POST operation to the specified URI with the specified string in the body of
/// the request.
pub async fn post(
    uri: Uri,
    body: &str,
    content_type: &str,
) -> Result<String, Box<dyn std::error::Error>> {
    info!("Posting '{}' as '{}' to {}", body, content_type, &uri);
    execute_request(
        Request::builder()
            .method("POST")
            .uri(uri)
            .header("Content-Type", content_type)
            .body(Body::from(body.to_owned()))?,
    )
    .await
}

/// Executes a request and ensures that the response code indicates success.
async fn execute_request(request: Request<Body>) -> Result<String, Box<dyn error::Error>> {
    let https = HttpsConnector::new();
    let client = Client::builder().build::<_, hyper::Body>(https);
    let response = client.request(request).await?;
    let status = response.status();
    info!("Response status: {}", &status);
    let buffer = aggregate(response).await?;
    let mut writer: Vec<u8> = vec![];
    copy(&mut buffer.reader(), &mut writer)?;
    let result = String::from_utf8(writer)?;
    info!("Received response: {}", &result);
    if status.is_success() {
        Ok(result)
    } else {
        Err(Box::new(HttpError::new(status)))
    }
}

/// Wrapper for storing HTTP status codes that indicate failure.
#[derive(Debug, Clone)]
pub struct HttpError {
    error_code: StatusCode,
}

impl HttpError {
    pub fn new(code: StatusCode) -> HttpError {
        HttpError { error_code: code }
    }
}

impl fmt::Display for HttpError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Authentication error: {}", &self.error_code)
    }
}

impl error::Error for HttpError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        // Source is not tracked.
        None
    }
}
