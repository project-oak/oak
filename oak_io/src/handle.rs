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
include!(concat!(env!("OUT_DIR"), "/oak.handle.rs"));

use crate::OakError;
use oak_abi::Handle;

/// Wrapper for a handle to the read half of a channel.
///
/// For use when the underlying [`Handle`] is known to be for a receive half.
#[derive(Copy, Clone, PartialEq)]
pub struct ReadHandle {
    pub handle: Handle,
}

impl std::fmt::Debug for ReadHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "ReadHandle({})", self.handle)
    }
}

impl From<Handle> for ReadHandle {
    fn from(handle: Handle) -> Self {
        ReadHandle { handle }
    }
}

/// Wrapper for a handle to the send half of a channel.
///
/// For use when the underlying [`Handle`] is known to be for a send half.
#[derive(Copy, Clone, PartialEq)]
pub struct WriteHandle {
    pub handle: Handle,
}

impl std::fmt::Debug for WriteHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "WriteHandle({})", self.handle)
    }
}

impl From<Handle> for WriteHandle {
    fn from(handle: Handle) -> Self {
        WriteHandle { handle }
    }
}

/// Visit all handles present in a type.
///
/// This trait can be automatically derived:
///
/// ```
/// use oak_io::{handle::HandleVisit, Handle};
///
/// #[derive(HandleVisit)]
/// struct Thing {
///     handle: Handle,
/// }
/// ```
///
/// Alternatively, you can implement the trait manually. This is required if you want the trait to
/// visit handles that are directly contained in a type.
///
/// ```
/// use oak_io::{handle::HandleVisit, Handle};
///
/// struct Thing {
///     handle: Handle,
/// }
///
/// impl HandleVisit for Thing {
///     fn visit<F: FnMut(&mut Handle)>(&mut self, mut visitor: F) -> F {
///         visitor(&mut self.handle);
///         visitor
///     }
///
///     fn fold<B, F: FnMut(B, &mut Handle) -> B>(&mut self, init: B, mut f: F) -> B {
///         f(init, &mut self.handle)
///     }
/// }
/// ```
pub trait HandleVisit {
    /// Invokes the provided closure on every handle contained in `self`.
    ///
    /// The mutable reference allows modifying the handles.
    fn visit<F: FnMut(&mut Handle)>(&mut self, visitor: F) -> F;

    fn fold<B, F: FnMut(B, &mut Handle) -> B>(&mut self, init: B, mut f: F) -> B {
        let mut accumulator = Some(init);
        let _ = self.visit(|handle| {
            accumulator = Some(f(accumulator.take().unwrap(), handle));
        });
        accumulator.unwrap()
    }
}

/// Return all handles in `T`.
///
/// Also sets all handles in `T` to `oak_abi::INVALID_HANDLE`.
///
/// The original message can be reconstructed by calling
/// [`inject_handles`](fn.inject_handles.html).
///
/// ```
/// use oak_io::{
///     handle::{extract_handles, HandleVisit},
///     Handle,
/// };
///
/// struct Thing {
///     handle: Handle,
/// }
/// # impl HandleVisit for Thing {
/// #   fn visit<F: FnMut(&mut Handle)>(&mut self, mut visitor: F) -> F {
/// #     visitor(&mut self.handle);
/// #     visitor
/// #   }
/// #
/// #   fn fold<B, F: FnMut(B, &mut Handle) -> B>(&mut self, init: B, mut f: F) -> B {
/// #       f(init, &mut self.handle)
/// #   }
/// # }
///
/// let mut thing = Thing { handle: 42 };
///
/// let handles = extract_handles(&mut thing);
///
/// assert_eq!(handles, vec![42]);
/// ```
pub fn extract_handles<T: HandleVisit>(msg: &mut T) -> Vec<Handle> {
    msg.fold(Vec::new(), |mut handles, handle| {
        handles.push(*handle);
        *handle = oak_abi::INVALID_HANDLE;
        handles
    })
}

/// Inject handles into a message.
///
/// If the number of handles provided is not exactly equal to the number of handles needed to fill
/// the message, an error is returned.
///
/// Order is significant: handles are injected in field declaration order, recursing
/// into nested structs before moving on to the next field.
///
/// ```
/// use oak_io::{
///     handle::{inject_handles, HandleVisit},
///     Handle,
/// };
///
/// # #[derive(Debug, PartialEq)]
/// struct Thing {
///     handle: Handle,
/// }
/// # impl HandleVisit for Thing {
/// #   fn visit<F: FnMut(&mut Handle)>(&mut self, mut visitor: F) -> F {
/// #     visitor(&mut self.handle);
/// #     visitor
/// #   }
/// #
/// #   fn fold<B, F: FnMut(B, &mut Handle) -> B>(&mut self, init: B, mut f: F) -> B {
/// #       f(init, &mut self.handle)
/// #   }
/// # }
///
/// let handles = vec![42];
/// let mut thing = Thing { handle: 0 };
///
/// inject_handles(&mut thing, &handles).unwrap();
///
/// assert_eq!(thing, Thing { handle: 42 });
/// ```
pub fn inject_handles<T: HandleVisit>(msg: &mut T, handles: &[Handle]) -> Result<(), OakError> {
    msg.fold(Ok(handles.iter()), |handles, handle| {
        let mut handles = handles?;
        let to_inject = handles.next().ok_or(OakError::ProtobufDecodeError(None))?;
        *handle = *to_inject;
        Ok(handles)
    })
    // Check that there are no remaining handles
    .and_then(|mut remaining_handles| {
        if remaining_handles.next().is_some() {
            Err(OakError::ProtobufDecodeError(None))
        } else {
            Ok(())
        }
    })
}

// A default implementation of the HandleVisit trait that does nothing
#[macro_export]
macro_rules! handle_visit_blanket_impl {
    ($($t:ty),+) => {
        $(
            impl HandleVisit for $t {
                fn visit<F: FnMut(&mut Handle)>(&mut self, visitor: F) -> F {
                    visitor
                }

                fn fold<B, F: FnMut(B, &mut Handle) -> B>(&mut self, init: B, _: F) -> B {
                    init
                }
            }
        )+
    };
}

// Provide an implementation for all scalar types in Prost.
// See: https://github.com/danburkert/prost#scalar-values
handle_visit_blanket_impl!((), f64, f32, i32, i64, u32, u64, bool, String, Vec<u8>);

// Provide an implementation for the Any and Timestamp types in Prost.
handle_visit_blanket_impl!(prost_types::Any, prost_types::Timestamp);

// Provide an implementation for oak_abi type that an implementation cannot be derived for.
// It does not contain handles, so a blanket impl is sufficient.
handle_visit_blanket_impl!(
    oak_abi::proto::oak::application::ConfigMap,
    oak_abi::proto::oak::label::Label
);

// Make the HandleVisit derivation macro publicly available without having to explicictly reference
// the oak_derive crate.
pub use oak_derive::HandleVisit;

// Implementations for the types generated from different field modifiers
// (https://github.com/danburkert/prost#scalar-values).

// Optional fields
impl<T: HandleVisit> HandleVisit for Option<T> {
    fn visit<F: FnMut(&mut Handle)>(&mut self, visitor: F) -> F {
        if let Some(inner) = self {
            inner.visit(visitor)
        } else {
            visitor
        }
    }

    fn fold<B, F: FnMut(B, &mut Handle) -> B>(&mut self, init: B, f: F) -> B {
        if let Some(inner) = self {
            inner.fold(init, f)
        } else {
            init
        }
    }
}

// For repeated fields.
impl<T: HandleVisit> HandleVisit for Vec<T> {
    fn visit<F: FnMut(&mut Handle)>(&mut self, visitor: F) -> F {
        self.iter_mut()
            .fold(visitor, |visitor, item| item.visit(visitor))
    }

    fn fold<B, F: FnMut(B, &mut Handle) -> B>(&mut self, init: B, mut f: F) -> B {
        self.iter_mut()
            .fold(init, |init, item| item.fold(init, &mut f))
    }
}

// For recursive messages.
impl<T: HandleVisit> HandleVisit for Box<T> {
    fn visit<F: FnMut(&mut Handle)>(&mut self, visitor: F) -> F {
        self.as_mut().visit(visitor)
    }

    fn fold<B, F: FnMut(B, &mut Handle) -> B>(&mut self, init: B, f: F) -> B {
        self.as_mut().fold(init, f)
    }
}

// For maps. This is only supported for maps that have a key implementing `Ord`, because we need to
// be able to define an order in which to inject/extract handles. Since protobuf only supports
// integral and string types for keys, having this constraint is fine.
//
// See https://developers.google.com/protocol-buffers/docs/proto3#maps for more details.
impl<K: Ord + core::hash::Hash, V: HandleVisit, S> HandleVisit
    for std::collections::HashMap<K, V, S>
{
    fn visit<F: FnMut(&mut Handle)>(&mut self, visitor: F) -> F {
        let mut entries: Vec<(&K, &mut V)> = self.iter_mut().collect();
        // Can be unstable because keys are guaranteed to be unique.
        entries.sort_unstable_by_key(|&(k, _)| k);
        entries
            .into_iter()
            .map(|(_, v)| v)
            .fold(visitor, |visitor, value| value.visit(visitor))
    }

    fn fold<B, F: FnMut(B, &mut Handle) -> B>(&mut self, init: B, mut f: F) -> B {
        let mut entries: Vec<(&K, &mut V)> = self.iter_mut().collect();
        // Can be unstable because keys are guaranteed to be unique.
        entries.sort_unstable_by_key(|&(k, _)| k);
        entries
            .into_iter()
            .map(|(_, v)| v)
            .fold(init, |init, value| value.fold(init, &mut f))
    }
}
