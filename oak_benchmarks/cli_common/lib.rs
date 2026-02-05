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

//! Shared utilities for host-side benchmark runners.
//!
//! This crate provides common functionality used by both `oak_cli` and
//! `linux_cli`, including TSC detection, timing utilities, CLI parsing,
//! and result formatting.

pub mod cli;
pub mod results;
pub mod tsc;

// Re-export commonly used items at crate root.
pub use cli::{DisplayBenchmarkType, OutputFormat, parse_benchmark_type};
pub use results::{BenchmarkMetrics, BenchmarkResult, format_result};
pub use tsc::{DEFAULT_TSC_FREQ_HZ, TscFreq, detect_tsc_freq, tsc_to_nanos};
