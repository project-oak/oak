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
/// }
/// ```
pub trait HandleVisit {
    /// Invokes the provided closure on every handle contained in `self`.
    ///
    /// The mutable reference allows modifying the handles.
    fn visit<F: FnMut(&mut Handle)>(&mut self, visitor: F) -> F;
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
/// # }
///
/// let mut thing = Thing { handle: 42 };
///
/// let handles = extract_handles(&mut thing);
///
/// assert_eq!(handles, vec![42]);
/// ```
pub fn extract_handles<T: HandleVisit>(msg: &mut T) -> Vec<Handle> {
    let mut handles = Vec::new();
    msg.visit(|handle: &mut Handle| {
        handles.push(*handle);
        *handle = oak_abi::INVALID_HANDLE;
    });
    handles
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
    let mut handles = handles.iter();
    let mut result = Ok(());
    msg.visit(|handle| {
        if let Some(to_inject) = handles.next() {
            *handle = *to_inject;
        } else {
            result = Err(OakError::ProtobufDecodeError(None));
        }
    });
    if handles.next().is_some() {
        result = Err(OakError::ProtobufDecodeError(None));
    }
    result
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
            }
        )+
    };
}

// Provide an implementation for all scalar types in Prost.
// See: https://github.com/danburkert/prost#scalar-values
handle_visit_blanket_impl!((), f64, f32, i32, i64, u32, u64, bool, String, Vec<u8>);

// Provide an implementation for the Any type in Prost.
handle_visit_blanket_impl!(prost_types::Any);

// Provide an implementation for oak_abi type that an implementation cannot be derived for.
// It does not contain handles, so a blanket impl is sufficient.
handle_visit_blanket_impl!(oak_abi::proto::oak::application::ConfigMap);

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
}

// For repeated fields.
impl<T: HandleVisit> HandleVisit for Vec<T> {
    fn visit<F: FnMut(&mut Handle)>(&mut self, visitor: F) -> F {
        self.iter_mut()
            .fold(visitor, |visitor, item| item.visit(visitor))
    }
}

// For recursive messages.
impl<T: HandleVisit> HandleVisit for Box<T> {
    fn visit<F: FnMut(&mut Handle)>(&mut self, visitor: F) -> F {
        self.as_mut().visit(visitor)
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
}
