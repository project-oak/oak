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

include!(concat!(env!("OUT_DIR"), "/handle_tests/tests.rs"));

use oak::{
    handle::{extract_handles, inject_handles},
    io::{Receiver, Sender},
};

#[test]
fn extract_nothing() {
    let mut message = LookMaNoHandles {
        a: "Hello, world!".to_string(),
        b: 42,
    };

    let handles = extract_handles(&mut message);

    assert_eq!(handles, vec![]);
}

#[test]
fn extract_struct() {
    let mut message = TestMessage {
        other_arbitrary_field: "Test".to_string(),
        test_sender: Some(sender(42)),
        test_receiver: Some(receiver(1337)),
    };

    let handles = extract_handles(&mut message);

    assert_eq!(handles, vec![42, 1337]);
    assert_eq!(
        message,
        TestMessage {
            other_arbitrary_field: "Test".to_string(),
            test_sender: Some(sender(0)),
            test_receiver: Some(receiver(0)),
        }
    );
}

#[test]
fn enum_extract_sender() {
    let mut message = TestMessageWithEnum {
        either: Some(test_message_with_enum::Either::EitherSender(sender(42))),
    };

    let handles = extract_handles(&mut message);

    assert_eq!(handles, vec![42]);
    assert_eq!(
        message,
        TestMessageWithEnum {
            either: Some(test_message_with_enum::Either::EitherSender(sender(0))),
        }
    );
}

#[test]
fn enum_extract_receiver() {
    let mut message = TestMessageWithEnum {
        either: Some(test_message_with_enum::Either::EitherReceiver(receiver(42))),
    };

    let handles = extract_handles(&mut message);

    assert_eq!(handles, vec![42]);
    assert_eq!(
        message,
        TestMessageWithEnum {
            either: Some(test_message_with_enum::Either::EitherReceiver(receiver(0))),
        }
    );
}

#[test]
fn enum_inject_sender() {
    let mut message = TestMessageWithEnum {
        either: Some(test_message_with_enum::Either::EitherSender(sender(0))),
    };

    inject_handles(&mut message, &[42]).unwrap();

    assert_eq!(
        message,
        TestMessageWithEnum {
            either: Some(test_message_with_enum::Either::EitherSender(sender(42))),
        }
    );
}

#[test]
fn map_extract() {
    use dummy_hash::DummyBuildHasher;
    use std::collections::HashMap;
    let mut map: HashMap<u64, Sender<()>, DummyBuildHasher> =
        HashMap::with_hasher(DummyBuildHasher);
    map.insert(1, sender(10));
    map.insert(2, sender(20));
    // DummyHasher should yield elements in reverse order.
    assert_eq!(
        map.values().cloned().collect::<Vec<Sender<()>>>(),
        vec![sender(20), sender(10)]
    );

    let handles = extract_handles(&mut map);

    // Even though the hashmap returns the values in reverse order, we expect the values to be
    // extracted in the order of their keys.
    assert_eq!(handles, vec![10, 20]);
}

#[test]
fn map_inject() {
    use dummy_hash::DummyBuildHasher;
    use std::collections::HashMap;
    let mut map: HashMap<u64, Sender<()>, DummyBuildHasher> =
        HashMap::with_hasher(DummyBuildHasher);
    map.insert(1, sender(0));
    map.insert(2, sender(0));

    inject_handles(&mut map, &[10, 20]).unwrap();

    assert_eq!(map.get(&1).cloned(), Some(sender(10)));
    assert_eq!(map.get(&2).cloned(), Some(sender(20)));
}

#[test]
fn recursive_extract() {
    let mut msg = RecursiveMessage {
        sender: None,
        recursive_message: Some(Box::new(RecursiveMessage {
            sender: Some(sender(42)),
            recursive_message: None,
        })),
    };

    let handles = extract_handles(&mut msg);

    assert_eq!(handles, vec![42]);
}

#[test]
fn repeated_extract() {
    let mut msg = RepeatedMessage {
        sender: vec![sender(1), sender(2), sender(3)],
    };

    let handles = extract_handles(&mut msg);

    assert_eq!(handles, vec![1, 2, 3]);
}

#[test]
fn inject_too_many_fails() {
    let mut message = TestMessage {
        other_arbitrary_field: "Test".to_string(),
        test_sender: Some(sender(0)),
        test_receiver: Some(receiver(0)),
    };

    let handles = vec![1, 2, 3];

    assert!(inject_handles(&mut message, &handles).is_err());
}

#[test]
fn inject_too_few_fails() {
    let mut message = TestMessage {
        other_arbitrary_field: "Test".to_string(),
        test_sender: Some(sender(0)),
        test_receiver: Some(receiver(0)),
    };

    let handles = vec![1];

    assert!(inject_handles(&mut message, &handles).is_err());
}

#[test]
fn sane_handle_order() {
    let reference = SaneHandleOrder {
        sender: Some(sender(1)),
        children: vec![
            SaneHandleOrder {
                sender: Some(sender(2)),
                children: vec![SaneHandleOrder {
                    sender: Some(sender(3)),
                    children: vec![],
                    receiver: Some(receiver(4)),
                }],
                receiver: Some(receiver(5)),
            },
            SaneHandleOrder {
                sender: Some(sender(6)),
                children: vec![],
                receiver: Some(receiver(7)),
            },
        ],
        receiver: Some(receiver(8)),
    };
    let mut message = reference.clone();

    let handles = extract_handles(&mut message);
    inject_handles(&mut message, &handles).expect("Failed to re-inject handles");

    assert_eq!(handles, vec![1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(reference, message);
}

#[test]
fn roundtrip() {
    let reference = RoundtripContainer {
        look_ma_no_handles: Some(LookMaNoHandles {
            a: "test".to_string(),
            b: 2,
        }),
        recursive_message: Some(RecursiveMessage {
            sender: Some(sender(1)),
            recursive_message: Some(Box::new(RecursiveMessage {
                sender: None,
                recursive_message: Some(Box::new(RecursiveMessage {
                    sender: Some(sender(2)),
                    recursive_message: None,
                })),
            })),
        }),
        repeated_message: Some(RepeatedMessage {
            sender: vec![sender(10), sender(9), sender(8)],
        }),
        sane_handle_order: Some(SaneHandleOrder {
            sender: Some(sender(10)),
            children: vec![SaneHandleOrder {
                sender: Some(sender(9)),
                children: vec![],
                receiver: Some(receiver(2)),
            }],
            receiver: Some(receiver(1)),
        }),
        test_message: Some(TestMessage {
            other_arbitrary_field: "test".to_string(),
            test_sender: Some(sender(1)),
            test_receiver: Some(receiver(2)),
        }),
        test_message_with_enum: Some(TestMessageWithEnum {
            either: Some(test_message_with_enum::Either::EitherReceiver(receiver(1))),
        }),
    };

    let mut message = reference.clone();

    let handles = extract_handles(&mut message);
    inject_handles(&mut message, &handles).expect("Failed to inject handles back");

    assert_eq!(reference, message);
}

fn sender<T: oak::io::Encodable>(id: u64) -> Sender<T> {
    Sender::new(oak::WriteHandle {
        handle: oak::Handle::from_raw(id),
    })
}

fn receiver<T: oak::io::Decodable>(id: u64) -> Receiver<T> {
    Receiver::new(oak::ReadHandle {
        handle: oak::Handle::from_raw(id),
    })
}

// Dummy hashing utilities to make the order of elements returned from a HashMap deterministic
// (reverse sorted order by key).
mod dummy_hash {
    use std::hash::{BuildHasher, Hasher};

    pub struct DummyHasher(u64);

    impl Hasher for DummyHasher {
        fn finish(&self) -> u64 {
            // Reverse the order
            core::u64::MAX - self.0
        }

        fn write(&mut self, bytes: &[u8]) {
            for b in bytes {
                self.0 += *b as u64;
            }
        }
    }

    pub struct DummyBuildHasher;

    impl BuildHasher for DummyBuildHasher {
        type Hasher = DummyHasher;

        fn build_hasher(&self) -> Self::Hasher {
            DummyHasher(0)
        }
    }
}
