// Copyright 2022 The Project Oak Authors
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

use oak_idl::*;

// An example of a (subset of) the Oak ABI expressed as an Oak Service.
//
// Note that this service is exposed on a single channel handle, and the numbers correspond to
// method identifiers within that channel.
service! {
    Oak {
        42 => fn lookup_data(key: Vec<u8>) -> Option<Vec<u8>>;
        10 => fn log(log: String) -> ();
    }
}

struct OakImpl;

impl Oak for OakImpl {
    fn lookup_data(&self, key: Vec<u8>) -> Option<Vec<u8>> {
        let h = maplit::hashmap! {
            vec![14, 12] => vec![19, 88]
        };
        h.get(&key).cloned()
    }

    #[allow(clippy::unused_unit)]
    fn log(&self, log: String) -> () {
        eprintln!("log: {log}");
    }
}

#[test]
fn foo() {
    let s = OakImpl;
    let transport = s.serve();
    let c = OakClient::new(transport);
    let res = c.lookup_data(vec![14, 12]).unwrap();
    assert_eq!(Some(vec![19, 88]), res);
}
