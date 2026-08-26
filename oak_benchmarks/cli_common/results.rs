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

//! Benchmark result metrics and formatting.

pub use benchmark::cpu::CpuFeatures;

use crate::{
    cli::{ByteSemantics, OutputFormat},
    dispersion::Distribution,
    tsc::tsc_to_nanos,
};

/// Calculated metrics from a benchmark response.
///
/// Two conventions are worth stating, because published tables differ on both.
///
/// The tick figures are **invariant-TSC ticks, not retired core cycles.** The
/// TSC advances at a fixed rate regardless of the frequency the core is
/// actually running at, so these are wall time in disguise, expressed in a unit
/// that happens to be comparable across the two platforms without calibrating
/// anything. Retired cycles would need a performance counter, which the enclave
/// cannot reach. Naming the field for what it measures is deliberate: it used
/// to be called `cycles_per_op`, which claimed more than it delivered.
///
/// Per-operation cost is reported in **both** ticks and nanoseconds, following
/// the form used by Unikraft's syscall table (EuroSys 2021, Table 1), which
/// prints `#Cycles` and `nsecs` in adjacent columns. Ticks are the honest
/// cross-platform comparison; nanoseconds are what a reader can sanity-check
/// against their own intuition.
#[derive(Debug, Clone, Copy)]
pub struct BenchmarkMetrics {
    /// Elapsed time in nanoseconds.
    ///
    /// Taken directly from the guest where a clock exists, otherwise derived
    /// from `elapsed_tsc` using the calibrated frequency.
    pub elapsed_ns: u64,
    /// Byte rate, in bytes per second.
    ///
    /// Only comparable between benchmarks whose [`ByteSemantics`] agree; see
    /// that type for why the same field counts different things.
    pub throughput_bps: f64,
    /// Operations (hashes, signatures, lookups, ...) per second.
    pub ops_per_sec: f64,
    /// Invariant-TSC ticks per operation.
    ///
    /// The headline cross-platform metric. Unlike every other field here it is
    /// computed purely from `elapsed_tsc` and the iteration count, so it does
    /// not depend on the TSC frequency being calibrated correctly and can be
    /// compared between the enclave and the Linux baseline without any
    /// conversion. `None` when the guest reported no TSC reading.
    pub tsc_ticks_per_op: Option<f64>,
    /// Nanoseconds per operation, printed beside the tick figure.
    ///
    /// Unlike [`Self::tsc_ticks_per_op`] this does depend on the calibrated
    /// frequency for the enclave, which has no clock of its own. `None` when
    /// no iterations completed.
    pub ns_per_op: Option<f64>,
    /// Invariant-TSC ticks per byte.
    ///
    /// `None` unless the benchmark's [`ByteSemantics`] make a per-byte figure
    /// comparable with published numbers, which in practice means the hash and
    /// AEAD rows. Emitting it for, say, the allocator benchmark would invite a
    /// comparison against eBACS that the number cannot support.
    pub tsc_ticks_per_byte: Option<f64>,
}

impl BenchmarkMetrics {
    /// Calculate metrics from raw benchmark data.
    ///
    /// Both platforms report `elapsed_tsc`. `elapsed_ns` is additionally
    /// reported by the Linux baseline, which has a real clock; when present it
    /// is preferred over converting from ticks, since it involves no
    /// calibration at all.
    ///
    /// `byte_semantics` decides only whether a per-byte figure is produced. It
    /// does not affect any other field.
    pub fn calculate(
        elapsed_tsc: u64,
        elapsed_ns: u64,
        iterations_completed: u32,
        bytes_processed: u64,
        tsc_freq: u64,
        byte_semantics: ByteSemantics,
    ) -> Self {
        // Use elapsed_ns directly if available, otherwise convert from TSC.
        let elapsed_ns =
            if elapsed_ns > 0 { elapsed_ns } else { tsc_to_nanos(elapsed_tsc, tsc_freq) };

        let throughput_bps = if elapsed_ns > 0 {
            bytes_processed as f64 / (elapsed_ns as f64 / 1_000_000_000.0)
        } else {
            0.0
        };

        let ops_per_sec = if elapsed_ns > 0 {
            (iterations_completed as f64) / (elapsed_ns as f64 / 1_000_000_000.0)
        } else {
            0.0
        };

        let tsc_ticks_per_op = if elapsed_tsc > 0 && iterations_completed > 0 {
            Some(elapsed_tsc as f64 / iterations_completed as f64)
        } else {
            None
        };

        let ns_per_op = if iterations_completed > 0 {
            Some(elapsed_ns as f64 / iterations_completed as f64)
        } else {
            None
        };

        let tsc_ticks_per_byte =
            if byte_semantics.supports_per_byte() && elapsed_tsc > 0 && bytes_processed > 0 {
                Some(elapsed_tsc as f64 / bytes_processed as f64)
            } else {
                None
            };

        Self {
            elapsed_ns,
            throughput_bps,
            ops_per_sec,
            tsc_ticks_per_op,
            ns_per_op,
            tsc_ticks_per_byte,
        }
    }

    /// Get throughput in MB/s for display purposes.
    pub fn throughput_mbps(&self) -> f64 {
        self.throughput_bps / 1_000_000.0
    }
}

/// Common fields needed for formatting benchmark results.
/// Proto-agnostic to work with both service::* and oak_proto_rust::* types.
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub benchmark_name: String,
    pub data_size: u32,
    pub iterations_completed: u32,
    pub elapsed_tsc: u64,
    pub elapsed_ns: u64,
    pub bytes_processed: u64,
    pub status: u32,
    /// What [`Self::bytes_processed`] counts for this benchmark.
    ///
    /// Carried on the result rather than looked up at format time so that a
    /// byte rate is never printed without the label that makes it meaningful.
    pub bytes: ByteSemantics,
    /// Actual working set size used by the guest, in bytes.
    pub working_set_size: u64,
    /// Checksum over the benchmark output.
    ///
    /// Must match between the enclave and the baseline for the same benchmark,
    /// seed and parameters.
    ///
    /// A match is weaker evidence than it looks. It witnesses the inputs and
    /// the loop, but not the hash function or the instruction set, and three
    /// benchmarks match for free. The `oak_benchmarks::benchmark` module
    /// documentation lists which and why.
    pub checksum: u64,
    /// Packed [`CpuFeatures`]: compile-time features, `CPUID` features and the
    /// runtime-dispatch flag. Layout is defined by `CpuFeatures::to_wire`.
    pub cpu_features: u32,
    /// What the guest measured, where the number needs it to be interpreted.
    ///
    /// The syscall benchmarks put the name of the syscall here. Empty
    /// otherwise.
    pub detail: String,
}

/// Human-readable description of a guest status code.
///
/// Delegates to the benchmark crate so the mapping has a single definition.
pub fn describe_status(status: u32) -> &'static str {
    benchmark::BenchmarkError::describe(status)
}

/// Convert a guest status code into a `Result`.
///
/// The host CLIs must call this before formatting a response. A failed
/// benchmark returns an all-zero response, and treating that as a real
/// measurement produced both nonsense results and, previously, a
/// divide-by-zero panic that hid the underlying error entirely.
pub fn check_status(status: u32) -> Result<(), String> {
    if status == 0 {
        Ok(())
    } else {
        Err(format!("guest benchmark failed with status {status}: {}", describe_status(status)))
    }
}

/// CSV header matching the column order produced by [`format_result`].
///
/// `cycles_per_op` was renamed to `tsc_ticks_per_op` when `ns_per_op` and
/// `tsc_ticks_per_byte` were added; anything parsing the old column name needs
/// updating.
pub fn csv_header() -> String {
    "benchmark,data_size,iterations,elapsed_tsc,elapsed_ns,bytes_processed,byte_semantics,\
     throughput_bps,ops_per_sec,tsc_ticks_per_op,ns_per_op,tsc_ticks_per_byte,working_set_size,\
     checksum,cpu_features,detail,status\n"
        .to_string()
}

/// Longest `detail` string the host will accept from a guest.
///
/// The values the suite actually produces are under 20 characters
/// (`write(-1,NULL,0)` is the longest). Generous enough not to truncate a
/// plausible future probe name, small enough that a garbled response cannot
/// flood a results table.
const MAX_DETAIL_LEN: usize = 64;

/// Bounds the guest-supplied `detail` string as it enters the host.
///
/// `detail` is the only free-form field crossing the wire, so bounding it once
/// here beats making every output format cope. Control characters would corrupt
/// a terminal and the length cap keeps a malformed response short. Quoting
/// stays the formatter's job, so commas and quotes are left alone.
pub fn sanitize_detail(detail: &str) -> String {
    detail.chars().filter(|c| !c.is_control()).take(MAX_DETAIL_LEN).collect()
}

/// Quotes a field for CSV output when it contains a character that would
/// otherwise change the shape of the row.
///
/// The enclave's null-syscall probe reports itself as `write(-1,NULL,0)`, whose
/// commas would turn a fourteen-field row into a sixteen-field one. `benchmark`
/// cannot currently contain a comma but is quoted on the same footing, so the
/// rule is a property of the column rather than of today's values.
///
/// See RFC 4180 section 2, <https://www.rfc-editor.org/rfc/rfc4180#section-2>.
fn csv_field(value: &str) -> String {
    if value.contains([',', '"', '\n', '\r']) {
        format!("\"{}\"", value.replace('"', "\"\""))
    } else {
        value.to_string()
    }
}

/// Escapes a string for use inside a JSON string literal.
///
/// The JSON output is assembled by string formatting rather than by a
/// serialiser, so the escaping that a serialiser would do has to happen here.
/// Covers the two characters that would terminate or re-open the literal, plus
/// the control characters, which RFC 8259 section 7 forbids unescaped.
/// <https://www.rfc-editor.org/rfc/rfc8259#section-7>
fn json_string(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for c in value.chars() {
        match c {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            c if (c as u32) < 0x20 => escaped.push_str(&format!("\\u{:04x}", c as u32)),
            c => escaped.push(c),
        }
    }
    escaped
}

/// Renders an optional figure, or `n/a`, at the given precision.
fn optional(value: Option<f64>, precision: usize) -> String {
    match value {
        Some(v) => format!("{v:.precision$}"),
        None => "n/a".to_string(),
    }
}

/// Renders an optional figure as a JSON number, or `null`.
///
/// NaN is not valid JSON, so an absent figure has to be `null` rather than the
/// float that `unwrap_or` would produce.
fn optional_json(value: Option<f64>, precision: usize) -> String {
    match value {
        Some(v) => format!("{v:.precision$}"),
        None => "null".to_string(),
    }
}

/// Format benchmark results for output.
pub fn format_result(
    result: &BenchmarkResult,
    metrics: &BenchmarkMetrics,
    format: OutputFormat,
) -> String {
    match format {
        OutputFormat::Human => {
            // Benchmarks that move no bytes have no byte rate; printing
            // "0.00 MB/s" for them reads as a measurement rather than as an
            // absent one. Where there is a rate, say what the bytes are: the
            // same field counts message bytes for a hash and
            // allocator-requested bytes for the churn benchmark, and those are
            // not the same quantity.
            let throughput = if result.bytes_processed == 0 {
                "n/a".to_string()
            } else {
                format!("{:.2} MB/s ({})", metrics.throughput_mbps(), result.bytes.label())
            };
            // Only shown where it is comparable with published cycles-per-byte
            // figures; see `ByteSemantics::supports_per_byte`.
            let per_byte = match metrics.tsc_ticks_per_byte {
                Some(v) => format!("TSC ticks/byte:      {v:.3}\n"),
                None => String::new(),
            };
            let detail = if result.detail.is_empty() {
                String::new()
            } else {
                format!("Measured:            {}\n", result.detail)
            };
            format!(
                "\n=== Benchmark Results ===\n\
                 Benchmark:           {}\n\
                 {}\
                 Data size:           {} bytes\n\
                 Iterations:          {}\n\
                 Working set:         {} bytes\n\
                 Guest elapsed (TSC): {} ticks\n\
                 Guest elapsed:       {:.3} ms\n\
                 Bytes processed:     {} ({})\n\
                 TSC ticks/op:        {}\n\
                 Nanoseconds/op:      {}\n\
                 {}\
                 Throughput:          {}\n\
                 Operations/sec:      {:.0}\n\
                 Checksum:            0x{:016x}\n\
                 CPU features:        {:#}\n\
                 Status:              {}\n\
                 \n\
                 Timebase is the invariant TSC, not retired core cycles.\n",
                result.benchmark_name,
                detail,
                result.data_size,
                result.iterations_completed,
                result.working_set_size,
                result.elapsed_tsc,
                metrics.elapsed_ns as f64 / 1_000_000.0,
                result.bytes_processed,
                result.bytes.label(),
                optional(metrics.tsc_ticks_per_op, 1),
                optional(metrics.ns_per_op, 2),
                per_byte,
                throughput,
                metrics.ops_per_sec,
                result.checksum,
                CpuFeatures::from_wire(result.cpu_features),
                if result.status == 0 { "OK" } else { "ERROR" },
            )
        }
        OutputFormat::Csv => {
            // Use base units (bytes/s) in machine-readable formats. An absent
            // figure is an empty field rather than a sentinel value.
            let optional_csv = |v: Option<f64>, p: usize| match v {
                Some(v) => format!("{v:.p$}"),
                None => String::new(),
            };
            format!(
                "{},{},{},{},{},{},{},{:.0},{:.0},{},{},{},{},{},{},{},{}\n",
                csv_field(&result.benchmark_name),
                result.data_size,
                result.iterations_completed,
                result.elapsed_tsc,
                metrics.elapsed_ns,
                result.bytes_processed,
                result.bytes.name(),
                metrics.throughput_bps,
                metrics.ops_per_sec,
                optional_csv(metrics.tsc_ticks_per_op, 3),
                optional_csv(metrics.ns_per_op, 3),
                optional_csv(metrics.tsc_ticks_per_byte, 4),
                result.working_set_size,
                result.checksum,
                result.cpu_features,
                csv_field(&result.detail),
                result.status,
            )
        }
        OutputFormat::Json => {
            // Use base units (bytes/s) in machine-readable formats.
            format!(
                r#"{{"benchmark":"{}","data_size":{},"iterations":{},"elapsed_tsc":{},"elapsed_ns":{},"bytes_processed":{},"byte_semantics":"{}","throughput_bps":{:.0},"ops_per_sec":{:.0},"tsc_ticks_per_op":{},"ns_per_op":{},"tsc_ticks_per_byte":{},"working_set_size":{},"checksum":{},"cpu_features":{},"detail":"{}","status":{}}}"#,
                json_string(&result.benchmark_name),
                result.data_size,
                result.iterations_completed,
                result.elapsed_tsc,
                metrics.elapsed_ns,
                result.bytes_processed,
                result.bytes.name(),
                metrics.throughput_bps,
                metrics.ops_per_sec,
                optional_json(metrics.tsc_ticks_per_op, 3),
                optional_json(metrics.ns_per_op, 3),
                optional_json(metrics.tsc_ticks_per_byte, 4),
                result.working_set_size,
                result.checksum,
                result.cpu_features,
                json_string(&result.detail),
                result.status,
            )
        }
    }
}

/// One repetition's raw readings and the metrics derived from them.
///
/// `elapsed_tsc` and `checksum` are carried per repetition rather than taken
/// from the final run. Reusing the last repetition's tick count for every row
/// of a machine-readable dump silently replaces the measurement with a copy of
/// one sample, which is worse than not emitting the column at all.
#[derive(Debug, Clone, Copy)]
pub struct Repetition {
    /// TSC ticks this repetition took.
    pub elapsed_tsc: u64,
    /// Checksum this repetition produced.
    pub checksum: u64,
    /// Metrics derived from this repetition alone.
    pub metrics: BenchmarkMetrics,
}

/// One benchmark measured several times over.
///
/// Holds every repetition rather than a running summary, so the individual
/// samples can be printed. That matters more than it sounds: the first
/// repetition of an allocator or page-fault benchmark is systematically
/// different from the rest, because the heap is cold, and a median would hide
/// that rather than reveal it.
#[derive(Debug, Clone)]
pub struct RepeatedRun {
    /// Metadata that does not vary between repetitions of the same request:
    /// benchmark name, requested sizes, CPU features, working set.
    ///
    /// Its `elapsed_tsc`, `elapsed_ns` and `checksum` fields are those of the
    /// final repetition and are overridden per row when formatting.
    pub result: BenchmarkResult,
    /// One entry per repetition, in the order they ran.
    pub repetitions: Vec<Repetition>,
}

impl RepeatedRun {
    /// Whether every repetition produced the same checksum.
    ///
    /// A disagreement means the repetitions did not all do the same thing, so
    /// pooling them into one distribution would be meaningless.
    pub fn checksums_agree(&self) -> bool {
        let mut checksums = self.repetitions.iter().map(|r| r.checksum);
        match checksums.next() {
            Some(first) => checksums.all(|c| c == first),
            None => true,
        }
    }

    /// Distribution of TSC ticks per operation, `None` if no repetition
    /// reported a TSC reading.
    pub fn tsc_ticks_per_op(&self) -> Option<Distribution> {
        self.distribution(|m| m.tsc_ticks_per_op)
    }

    /// Distribution of nanoseconds per operation.
    pub fn ns_per_op(&self) -> Option<Distribution> {
        self.distribution(|m| m.ns_per_op)
    }

    /// Distribution of TSC ticks per byte, `None` unless the benchmark's byte
    /// semantics make a per-byte figure meaningful.
    pub fn tsc_ticks_per_byte(&self) -> Option<Distribution> {
        self.distribution(|m| m.tsc_ticks_per_byte)
    }

    /// Distribution of operations per second.
    pub fn ops_per_sec(&self) -> Option<Distribution> {
        self.distribution(|m| Some(m.ops_per_sec))
    }

    fn distribution(
        &self,
        extract: impl Fn(&BenchmarkMetrics) -> Option<f64>,
    ) -> Option<Distribution> {
        let mut samples: Vec<f64> =
            self.repetitions.iter().filter_map(|r| extract(&r.metrics)).collect();
        Distribution::from_samples(&mut samples)
    }

    /// The result as it stood for one repetition, for per-row formatting.
    fn result_for(&self, repetition: &Repetition) -> BenchmarkResult {
        BenchmarkResult {
            elapsed_tsc: repetition.elapsed_tsc,
            elapsed_ns: repetition.metrics.elapsed_ns,
            checksum: repetition.checksum,
            ..self.result.clone()
        }
    }
}

/// Renders a distribution as `median [q1, q3] n=N`, the form the suite quotes.
fn summarize(distribution: Option<Distribution>, precision: usize) -> String {
    match distribution {
        Some(d) => {
            let spread = match d.relative_iqr() {
                Some(r) => format!(" IQR={:.1}%", r * 100.0),
                None => String::new(),
            };
            format!(
                "{:.precision$} [{:.precision$}, {:.precision$}] n={}{}",
                d.median, d.q1, d.q3, d.n, spread
            )
        }
        None => "n/a".to_string(),
    }
}

/// Format a repeated run.
///
/// The human form leads with the median and quartiles and then lists every
/// sample, because a cold first repetition is a fact about the benchmark and
/// not noise to be averaged away. CSV and JSON emit one record per repetition,
/// carrying that repetition's own readings, leaving aggregation to whatever
/// consumes them.
pub fn format_repeated(run: &RepeatedRun, format: OutputFormat) -> String {
    match format {
        OutputFormat::Human => {
            let per_byte = match run.tsc_ticks_per_byte() {
                Some(d) => format!("TSC ticks/byte:      {}\n", summarize(Some(d), 3)),
                None => String::new(),
            };
            let samples: Vec<String> = run
                .repetitions
                .iter()
                .map(|r| match r.metrics.tsc_ticks_per_op {
                    Some(v) => format!("{v:.1}"),
                    None => "n/a".to_string(),
                })
                .collect();
            let checksum_warning = if run.checksums_agree() {
                String::new()
            } else {
                "\n\nWARNING: repetitions disagreed on the checksum, so they did not all do\n\
                 the same work and this summary is not meaningful."
                    .to_string()
            };
            let detail = if run.result.detail.is_empty() {
                String::new()
            } else {
                format!("Measured:            {}\n", run.result.detail)
            };
            format!(
                "\n=== Benchmark Results ({} repetitions) ===\n\
                 Benchmark:           {}\n\
                 {}\
                 Data size:           {} bytes\n\
                 Iterations:          {} per repetition\n\
                 Working set:         {} bytes\n\
                 Bytes processed:     {} per repetition ({})\n\
                 TSC ticks/op:        {}\n\
                 Nanoseconds/op:      {}\n\
                 {}\
                 Operations/sec:      {}\n\
                 Checksum:            0x{:016x}\n\
                 CPU features:        {:#}\n\
                 \n\
                 Per-repetition TSC ticks/op, in run order:\n  {}\n\
                 \n\
                 Figures are median [q1, q3] over n repetitions. Timebase is the\n\
                 invariant TSC, not retired core cycles.{}\n",
                run.repetitions.len(),
                run.result.benchmark_name,
                detail,
                run.result.data_size,
                run.result.iterations_completed,
                run.result.working_set_size,
                run.result.bytes_processed,
                run.result.bytes.label(),
                summarize(run.tsc_ticks_per_op(), 1),
                summarize(run.ns_per_op(), 2),
                per_byte,
                summarize(run.ops_per_sec(), 0),
                run.result.checksum,
                CpuFeatures::from_wire(run.result.cpu_features),
                samples.join(", "),
                checksum_warning,
            )
        }
        // One record per repetition, so no aggregation choice is baked in.
        // CSV rows already end in a newline; JSON objects do not, so they are
        // joined into JSON Lines rather than concatenated into one long line.
        OutputFormat::Csv | OutputFormat::Json => {
            let records: Vec<String> = run
                .repetitions
                .iter()
                .enumerate()
                .map(|(index, repetition)| {
                    let result = run.result_for(repetition);
                    with_repetition(
                        index,
                        &format_result(&result, &repetition.metrics, format),
                        format,
                    )
                })
                .collect();
            match format {
                OutputFormat::Json => format!("{}\n", records.join("\n")),
                _ => records.concat(),
            }
        }
    }
}

/// Adds a repetition index to a formatted single-run record.
fn with_repetition(index: usize, record: &str, format: OutputFormat) -> String {
    match format {
        // Prepend the index, matching `repeated_csv_header`.
        OutputFormat::Csv => format!("{index},{record}"),
        // Splice into the opening brace, so the field leads the object.
        OutputFormat::Json => match record.strip_prefix('{') {
            Some(rest) => format!("{{\"repetition\":{index},{rest}"),
            None => record.to_string(),
        },
        OutputFormat::Human => record.to_string(),
    }
}

/// CSV header for [`format_repeated`], which prefixes a repetition index.
pub fn repeated_csv_header() -> String {
    format!("repetition,{}", csv_header())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Metrics for a benchmark that moves no bytes, which is most of them.
    fn metrics(
        elapsed_tsc: u64,
        elapsed_ns: u64,
        iterations: u32,
        tsc_freq: u64,
    ) -> BenchmarkMetrics {
        BenchmarkMetrics::calculate(
            elapsed_tsc,
            elapsed_ns,
            iterations,
            0,
            tsc_freq,
            ByteSemantics::None,
        )
    }

    #[test]
    fn tsc_ticks_per_op_is_frequency_independent() {
        // Same ticks and iterations, wildly different assumed frequencies.
        let a = metrics(1_000_000, 0, 1_000, 1_000_000_000);
        let b = metrics(1_000_000, 0, 1_000, 5_000_000_000);
        assert_eq!(a.tsc_ticks_per_op, b.tsc_ticks_per_op);
        assert_eq!(a.tsc_ticks_per_op, Some(1_000.0));
        // ...whereas the nanosecond figures do depend on it.
        assert_ne!(a.elapsed_ns, b.elapsed_ns);
        assert_ne!(a.ns_per_op, b.ns_per_op);
    }

    #[test]
    fn tsc_ticks_per_op_absent_without_tsc() {
        assert_eq!(metrics(0, 1_000_000, 1_000, 1_000_000_000).tsc_ticks_per_op, None);
    }

    /// The nanosecond figure is what a reader sanity-checks against intuition,
    /// so it has to be present even where the tick figure is not.
    #[test]
    fn ns_per_op_accompanies_every_measured_run() {
        let m = metrics(0, 1_000_000, 1_000, 1_000_000_000);
        assert_eq!(m.ns_per_op, Some(1_000.0));

        // 1000 ticks at 1 GHz is 1000 ns, over 10 iterations.
        let converted = metrics(1_000, 0, 10, 1_000_000_000);
        assert_eq!(converted.tsc_ticks_per_op, Some(100.0));
        assert_eq!(converted.ns_per_op, Some(100.0));
    }

    /// Per-byte figures invite comparison against published cycles-per-byte
    /// tables, so they are emitted only where that comparison is valid.
    #[test]
    fn ticks_per_byte_only_for_message_bytes() {
        let message = BenchmarkMetrics::calculate(4_096, 0, 4, 4_096, 1, ByteSemantics::Message);
        assert_eq!(message.tsc_ticks_per_byte, Some(1.0));

        for semantics in [ByteSemantics::Payload, ByteSemantics::Requested, ByteSemantics::Written]
        {
            let m = BenchmarkMetrics::calculate(4_096, 0, 4, 4_096, 1, semantics);
            assert_eq!(m.tsc_ticks_per_byte, None, "{semantics:?} should not report per-byte");
        }
    }

    #[test]
    fn elapsed_ns_is_preferred_over_conversion() {
        // A deliberately wrong frequency must not affect the reported time
        // when the guest supplied real nanoseconds.
        assert_eq!(metrics(999_999_999, 2_000_000, 10, 1).elapsed_ns, 2_000_000);
    }

    #[test]
    fn zero_everything_does_not_panic_or_divide_by_zero() {
        let m = metrics(0, 0, 0, 0);
        assert_eq!(m.elapsed_ns, 0);
        assert_eq!(m.throughput_bps, 0.0);
        assert_eq!(m.ops_per_sec, 0.0);
        assert_eq!(m.tsc_ticks_per_op, None);
        assert_eq!(m.ns_per_op, None);
        assert_eq!(m.tsc_ticks_per_byte, None);
    }

    /// Runtime dispatch is what makes the `CPUID` half count, so the report has
    /// to reflect it.
    #[test]
    fn cpu_features_decode_matches_the_owning_crate() {
        let features = CpuFeatures::from_wire((0b11_1111 << 8) | (1 << 16));
        assert!(features.runtime_dispatch);
        assert_eq!(
            features.to_string(),
            "SHA_NI | AES_NI | PCLMULQDQ | AVX2 | AVX512IFMA | AVX512VL"
        );

        // Without dispatch the CPUID half is unreachable and must not appear.
        assert_eq!(CpuFeatures::from_wire(0b11_1111 << 8).to_string(), "none");
    }

    fn sample_result() -> BenchmarkResult {
        BenchmarkResult {
            benchmark_name: "x".to_string(),
            data_size: 1,
            iterations_completed: 1,
            elapsed_tsc: 1,
            elapsed_ns: 1,
            bytes_processed: 1,
            status: 0,
            bytes: ByteSemantics::Message,
            working_set_size: 1,
            checksum: 1,
            cpu_features: 1,
            detail: String::new(),
        }
    }

    #[test]
    fn csv_header_matches_row_column_count() {
        let result = sample_result();
        let metrics =
            BenchmarkMetrics::calculate(1, 1, 1, 1, 1_000_000_000, ByteSemantics::Message);
        let row = format_result(&result, &metrics, OutputFormat::Csv);
        assert_eq!(
            csv_header().trim_end().split(',').count(),
            row.trim_end().split(',').count(),
            "CSV header and row column counts disagree"
        );
    }

    /// A benchmark that moves no bytes has no throughput, and printing zero
    /// for it reads as a measurement rather than as an absent one.
    #[test]
    fn throughput_is_omitted_when_no_bytes_move() {
        let mut result = sample_result();
        result.bytes_processed = 0;
        let metrics =
            BenchmarkMetrics::calculate(1, 1, 0, 1, 1_000_000_000, ByteSemantics::Message);
        let text = format_result(&result, &metrics, OutputFormat::Human);
        assert!(text.contains("Throughput:          n/a"), "{text}");
        assert!(!text.contains("MB/s"), "{text}");
    }

    /// The syscall benchmarks are only interpretable with the name of the
    /// syscall, so it has to survive into every output format.
    #[test]
    fn the_detail_reaches_every_output_format() {
        let mut result = sample_result();
        result.detail = "getppid()".to_string();
        let metrics =
            BenchmarkMetrics::calculate(1, 1, 1, 1, 1_000_000_000, ByteSemantics::Message);
        for format in [OutputFormat::Human, OutputFormat::Csv, OutputFormat::Json] {
            assert!(
                format_result(&result, &metrics, format).contains("getppid()"),
                "{format:?} dropped the detail"
            );
        }
    }

    /// The enclave reports its probe as `write(-1,NULL,0)`. Emitted raw those
    /// commas add two fields to the row, and the sweep harness drops rows
    /// whose field count is wrong, so the enclave side of this benchmark
    /// silently produced no data at all.
    #[test]
    fn a_detail_containing_commas_stays_in_one_csv_field() {
        let mut result = sample_result();
        result.detail = "write(-1,NULL,0)".to_string();
        let metrics =
            BenchmarkMetrics::calculate(1, 1, 1, 1, 1_000_000_000, ByteSemantics::Message);
        let row = format_result(&result, &metrics, OutputFormat::Csv);

        let header_columns = csv_header().trim_end().split(',').count();
        assert_eq!(
            parse_csv_row(row.trim_end()).len(),
            header_columns,
            "row does not have one field per header column: {row}"
        );
        assert!(row.contains("\"write(-1,NULL,0)\""), "{row}");
    }

    /// A quote inside a quoted field is doubled, per RFC 4180.
    #[test]
    fn a_detail_containing_a_quote_is_doubled() {
        assert_eq!(csv_field(r#"a,"b""#), r#""a,""b""""#);
        assert_eq!(csv_field("plain"), "plain");
    }

    /// The guest's string is bounded once at ingestion. Commas and quotes
    /// survive, because they are legitimate in a syscall signature and the
    /// formatters quote them; control characters and excess length do not.
    #[test]
    fn ingestion_bounds_the_detail_without_breaking_it() {
        assert_eq!(sanitize_detail("write(-1,NULL,0)"), "write(-1,NULL,0)");
        assert_eq!(sanitize_detail("get\u{7}ppid\n()"), "getppid()");
        assert_eq!(sanitize_detail(&"x".repeat(200)).len(), MAX_DETAIL_LEN);
    }

    /// The JSON output is built by string formatting, so a quote in a
    /// free-form field would otherwise close the string literal and produce
    /// output that no parser accepts.
    #[test]
    fn json_output_escapes_quotes_and_control_characters() {
        assert_eq!(json_string(r#"say "hi"\"#), r#"say \"hi\"\\"#);
        assert_eq!(json_string("a\nb\u{1}"), "a\\nb\\u0001");
    }

    /// Splits a CSV row into fields, honouring RFC 4180 quoting.
    ///
    /// Only used by the tests, and only correct enough for them: it does not
    /// handle embedded newlines, which no field here can contain.
    fn parse_csv_row(row: &str) -> Vec<String> {
        let mut fields = Vec::new();
        let mut current = String::new();
        let mut in_quotes = false;
        let mut chars = row.chars().peekable();
        while let Some(c) = chars.next() {
            match c {
                '"' if in_quotes && chars.peek() == Some(&'"') => {
                    current.push('"');
                    chars.next();
                }
                '"' => in_quotes = !in_quotes,
                ',' if !in_quotes => fields.push(core::mem::take(&mut current)),
                c => current.push(c),
            }
        }
        fields.push(current);
        fields
    }
}
