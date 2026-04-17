//
// Copyright 2026 The Project Oak Authors
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

//! Memory-bound benchmark implementations.
//!
//! These benchmarks stress memory subsystem performance with large working
//! sets to evaluate allocator efficiency and memory access patterns.

pub mod alloc_churn;
pub mod array_update;
pub mod hashmap;

pub use alloc_churn::AllocChurnBenchmark;
pub use array_update::ArrayUpdateBenchmark;
pub use hashmap::{HashMapBenchmark, HashMapMode};

/// Trait for memory-bound benchmarks.
///
/// These benchmarks use large working sets to stress the memory subsystem.
pub trait MemoryBenchmark {
    /// Size of the working set in bytes.
    fn working_set_size(&self) -> usize;
}
