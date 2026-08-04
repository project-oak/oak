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

use procfs::{Current, Meminfo};

// Default min available memory ratio of 5%
pub const DEFAULT_MIN_AVAILABLE_MEMORY_RATIO: f64 = 0.05;

/// Memory usage information wrapper over procfs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemoryInfo {
    /// Total usable RAM in bytes.
    pub total_bytes: u64,
    /// Available RAM in bytes.
    pub available_bytes: u64,
}

impl MemoryInfo {
    /// Reads current memory info using `procfs`.
    pub fn current() -> Result<Self, anyhow::Error> {
        let meminfo = Meminfo::current()?;
        let available_bytes = meminfo
            .mem_available
            .ok_or_else(|| anyhow::anyhow!("MemAvailable not found in /proc/meminfo"))?;
        Ok(Self { total_bytes: meminfo.mem_total, available_bytes })
    }

    /// Calculates the ratio of available memory to total memory (between 0.0
    /// and 1.0).
    pub fn available_ratio(&self) -> f64 {
        assert!(
            self.total_bytes > 0,
            "MemTotal from /proc/meminfo is zero; cannot compute memory ratio"
        );
        (self.available_bytes as f64 / self.total_bytes as f64).clamp(0.0, 1.0)
    }

    /// Returns true if available memory ratio is below the given threshold
    /// ratio.
    pub fn is_below_threshold(&self, threshold_ratio: f64) -> bool {
        self.available_ratio() < threshold_ratio
    }
}

/// Helper function to maintain compatibility with `app/service.rs`.
pub fn read_system_meminfo() -> Result<MemoryInfo, anyhow::Error> {
    MemoryInfo::current()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "MemTotal from /proc/meminfo is zero")]
    fn test_zero_total_memory_safety() {
        let meminfo = MemoryInfo { total_bytes: 0, available_bytes: 0 };
        meminfo.available_ratio();
    }

    #[test]
    fn test_ratio_calculation() {
        let meminfo = MemoryInfo { total_bytes: 1000, available_bytes: 500 };
        assert!((meminfo.available_ratio() - 0.50).abs() < 0.001);
        assert!(!meminfo.is_below_threshold(DEFAULT_MIN_AVAILABLE_MEMORY_RATIO));

        let meminfo_low = MemoryInfo { total_bytes: 1000, available_bytes: 40 };
        assert!((meminfo_low.available_ratio() - 0.04).abs() < 0.001);
        assert!(meminfo_low.is_below_threshold(DEFAULT_MIN_AVAILABLE_MEMORY_RATIO));
    }
}
// Trigger Kokoro rerun again
// trigger kokoro
