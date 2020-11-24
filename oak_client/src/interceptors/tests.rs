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

use super::Interceptor;
use tonic::{Request, Status};

struct TestInterceptor {
    metadata_to_append: (&'static str, &'static str),
}

impl Interceptor for TestInterceptor {
    fn process(&self, request: Request<()>) -> Result<Request<()>, Status> {
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
    let combined = super::combine(
        TestInterceptor {
            metadata_to_append: ("foo_0", "bar_0"),
        },
        TestInterceptor {
            metadata_to_append: ("foo_1", "bar_1"),
        },
    );
    let initial = tonic::Request::new(());
    let processed = combined.process(initial).unwrap();
    let metadata = processed.metadata();
    assert_eq!(2, metadata.len());
    assert_eq!(
        vec!["bar_0"],
        metadata.get_all("foo_0").iter().collect::<Vec<_>>()
    );
    assert_eq!(
        vec!["bar_1"],
        metadata.get_all("foo_1").iter().collect::<Vec<_>>()
    );
}

#[test]
fn test_combine_same_key() {
    let combined = super::combine(
        TestInterceptor {
            metadata_to_append: ("foo", "bar_0"),
        },
        TestInterceptor {
            metadata_to_append: ("foo", "bar_1"),
        },
    );
    let initial = tonic::Request::new(());
    let processed = combined.process(initial).unwrap();
    let metadata = processed.metadata();
    assert_eq!(2, metadata.len());
    assert_eq!(
        vec!["bar_0", "bar_1"],
        metadata.get_all("foo").iter().collect::<Vec<_>>()
    );
}
