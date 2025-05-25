//
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

//! Utils to read the CPUs timestamp counter.

/// Read the timestamp counter register from the CPU.
///
/// The timestamp counter is incremented once every CPU clock cycle, and how it
/// behaves across power management events (e.g. change in P-state) is
/// CPU-depdendent.
///
/// See RDTSC in AMD64 Architecture Programmer's Manual, Volume 3 for more
/// details.
pub fn rdtsc() -> u64 {
    let mut edx: u64;
    let mut eax: u64;

    // Safety: `rdtsc` does not reference memory at all, so it's safe.
    unsafe {
        core::arch::asm!(
            "rdtsc",
            out("edx") edx,
            out("eax") eax,
            options(nomem, nostack)
        )
    }

    (edx << 32) | eax
}

/// Measures the number of clock cycles between `new()` and `elapsed()`.
///
/// This measurement only makes sense if the process is running on the same CPU,
/// as different CPUs will have different tick counter values.
#[derive(Debug)]
pub struct Timer {
    start: u64,
}

impl Timer {
    pub fn new(start: u64) -> Self {
        Self { start }
    }

    /// Constructs a new timer, recording the current tick counter value.
    pub fn new_rdtsc() -> Self {
        Self::new(rdtsc())
    }

    /// Returns the approximate number of clock cycles it took to execute
    /// `func`.
    pub fn timed<F>(func: F) -> u64
    where
        F: FnOnce(),
    {
        let timer = Timer::new_rdtsc();
        func();
        timer.elapsed()
    }

    /// Returns the approximate number of clock cycles elapsed since the
    /// construction of the `Timer`.
    pub fn elapsed(&self) -> u64 {
        let stop = rdtsc();
        stop - self.start
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn simple_timer() {
        let timer = Timer::new_rdtsc();
        let duration = timer.elapsed();
        assert!(duration > 0);
    }

    #[test]
    pub fn timed() {
        let duration = Timer::timed(|| {});
        assert!(duration > 0);
    }
}
