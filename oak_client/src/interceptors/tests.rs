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

use tonic::{service::interceptor::Interceptor, Request, Status};

#[derive(Clone)]
struct TestInterceptor {
    metadata_to_append: (&'static str, &'static str),
}

impl Interceptor for TestInterceptor {
    fn call(&mut self, request: Request<()>) -> Result<Request<()>, Status> {
        let mut request = request;
        request.metadata_mut().append(
            self.metadata_to_append.0,
            self.metadata_to_append.1.parse().unwrap(),
        );
        Ok(request)
    }
}

#[test]
fn test_combine_different_keys() {
    let mut combined = super::combine(
        TestInterceptor {
            metadata_to_append: ("key_0", "value_0"),
        },
        TestInterceptor {
            metadata_to_append: ("key_1", "value_1"),
        },
    );
    let initial = tonic::Request::new(());
    let processed = combined.call(initial).unwrap();
    let metadata = processed.metadata();
    assert_eq!(2, metadata.len());
    assert_eq!(
        vec!["value_0"],
        metadata.get_all("key_0").iter().collect::<Vec<_>>()
    );
    assert_eq!(
        vec!["value_1"],
        metadata.get_all("key_1").iter().collect::<Vec<_>>()
    );
}

#[test]
fn test_combine_same_key() {
    let mut combined = super::combine(
        TestInterceptor {
            metadata_to_append: ("key", "value_0"),
        },
        TestInterceptor {
            metadata_to_append: ("key", "value_1"),
        },
    );
    let initial = tonic::Request::new(());
    let processed = combined.call(initial).unwrap();
    let metadata = processed.metadata();
    assert_eq!(2, metadata.len());
    assert_eq!(
        vec!["value_0", "value_1"],
        metadata.get_all("key").iter().collect::<Vec<_>>()
    );
}
