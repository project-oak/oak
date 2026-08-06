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

use crate::{cli::OutputFormat, tsc::tsc_to_nanos};

/// Calculated metrics from a benchmark response.
#[derive(Debug, Clone, Copy)]
pub struct BenchmarkMetrics {
    /// Elapsed time in nanoseconds.
    ///
    /// Taken directly from the guest where a clock exists, otherwise derived
    /// from `elapsed_tsc` using the calibrated frequency.
    pub elapsed_ns: u64,
    /// Throughput in bytes per second (base unit).
    pub throughput_bps: f64,
    /// Operations (hashes, signatures, lookups, ...) per second.
    pub ops_per_sec: f64,
    /// TSC ticks per operation.
    ///
    /// This is the headline cross-platform metric. Unlike every other field
    /// here it is computed purely from `elapsed_tsc` and the iteration count,
    /// so it does not depend on the TSC frequency being calibrated correctly
    /// and can be compared between the enclave and the Linux baseline without
    /// any conversion. `None` when the guest reported no TSC reading.
    pub cycles_per_op: Option<f64>,
}

impl BenchmarkMetrics {
    /// Calculate metrics from raw benchmark data.
    ///
    /// Both platforms now report `elapsed_tsc`. `elapsed_ns` is additionally
    /// reported by the Linux baseline, which has a real clock; when present it
    /// is preferred over converting from ticks, since it involves no
    /// calibration at all.
    pub fn calculate(
        elapsed_tsc: u64,
        elapsed_ns: u64,
        iterations_completed: u32,
        bytes_processed: u64,
        tsc_freq: u64,
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

        let cycles_per_op = if elapsed_tsc > 0 && iterations_completed > 0 {
            Some(elapsed_tsc as f64 / iterations_completed as f64)
        } else {
            None
        };

        Self { elapsed_ns, throughput_bps, ops_per_sec, cycles_per_op }
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
    /// Actual working set size used by the guest, in bytes.
    pub working_set_size: u64,
    /// Checksum over the benchmark output.
    ///
    /// Must match between the enclave and the baseline for the same benchmark,
    /// seed and parameters. A mismatch means the two sides did different work
    /// and the comparison is invalid.
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
pub fn csv_header() -> String {
    "benchmark,data_size,iterations,elapsed_tsc,elapsed_ns,bytes_processed,throughput_bps,\
     ops_per_sec,cycles_per_op,working_set_size,checksum,cpu_features,detail,status\n"
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

/// Format benchmark results for output.
pub fn format_result(
    result: &BenchmarkResult,
    metrics: &BenchmarkMetrics,
    format: OutputFormat,
) -> String {
    let cycles_per_op = metrics.cycles_per_op.unwrap_or(f64::NAN);
    match format {
        OutputFormat::Human => {
            // Benchmarks that move no bytes have no throughput; printing
            // "0.00 MB/s" for them reads as a measurement rather than as an
            // absent one.
            let throughput = if result.bytes_processed == 0 {
                "n/a".to_string()
            } else {
                format!("{:.2} MB/s", metrics.throughput_mbps())
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
                 Bytes processed:     {}\n\
                 Cycles/op:           {:.1}\n\
                 Throughput:          {}\n\
                 Operations/sec:      {:.0}\n\
                 Checksum:            0x{:016x}\n\
                 CPU features:        {:#}\n\
                 Status:              {}\n",
                result.benchmark_name,
                detail,
                result.data_size,
                result.iterations_completed,
                result.working_set_size,
                result.elapsed_tsc,
                metrics.elapsed_ns as f64 / 1_000_000.0,
                result.bytes_processed,
                cycles_per_op,
                throughput,
                metrics.ops_per_sec,
                result.checksum,
                CpuFeatures::from_wire(result.cpu_features),
                if result.status == 0 { "OK" } else { "ERROR" },
            )
        }
        OutputFormat::Csv => {
            // Use base units (bytes/s) in machine-readable formats.
            format!(
                "{},{},{},{},{},{},{:.0},{:.0},{:.3},{},{},{},{},{}\n",
                csv_field(&result.benchmark_name),
                result.data_size,
                result.iterations_completed,
                result.elapsed_tsc,
                metrics.elapsed_ns,
                result.bytes_processed,
                metrics.throughput_bps,
                metrics.ops_per_sec,
                cycles_per_op,
                result.working_set_size,
                result.checksum,
                result.cpu_features,
                csv_field(&result.detail),
                result.status,
            )
        }
        OutputFormat::Json => {
            // Use base units (bytes/s) in machine-readable formats.
            // `cycles_per_op` is emitted as null rather than NaN when absent,
            // because NaN is not valid JSON.
            let cycles_json = match metrics.cycles_per_op {
                Some(v) => format!("{v:.3}"),
                None => "null".to_string(),
            };
            format!(
                r#"{{"benchmark":"{}","data_size":{},"iterations":{},"elapsed_tsc":{},"elapsed_ns":{},"bytes_processed":{},"throughput_bps":{:.0},"ops_per_sec":{:.0},"cycles_per_op":{},"working_set_size":{},"checksum":{},"cpu_features":{},"detail":"{}","status":{}}}"#,
                json_string(&result.benchmark_name),
                result.data_size,
                result.iterations_completed,
                result.elapsed_tsc,
                metrics.elapsed_ns,
                result.bytes_processed,
                metrics.throughput_bps,
                metrics.ops_per_sec,
                cycles_json,
                result.working_set_size,
                result.checksum,
                result.cpu_features,
                json_string(&result.detail),
                result.status,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cycles_per_op_is_frequency_independent() {
        // Same ticks and iterations, wildly different assumed frequencies.
        let a = BenchmarkMetrics::calculate(1_000_000, 0, 1_000, 0, 1_000_000_000);
        let b = BenchmarkMetrics::calculate(1_000_000, 0, 1_000, 0, 5_000_000_000);
        assert_eq!(a.cycles_per_op, b.cycles_per_op);
        assert_eq!(a.cycles_per_op, Some(1_000.0));
        // ...whereas the nanosecond figure does depend on it.
        assert_ne!(a.elapsed_ns, b.elapsed_ns);
    }

    #[test]
    fn cycles_per_op_absent_without_tsc() {
        let m = BenchmarkMetrics::calculate(0, 1_000_000, 1_000, 0, 1_000_000_000);
        assert_eq!(m.cycles_per_op, None);
    }

    #[test]
    fn elapsed_ns_is_preferred_over_conversion() {
        // A deliberately wrong frequency must not affect the reported time
        // when the guest supplied real nanoseconds.
        let m = BenchmarkMetrics::calculate(999_999_999, 2_000_000, 10, 0, 1);
        assert_eq!(m.elapsed_ns, 2_000_000);
    }

    #[test]
    fn zero_everything_does_not_panic_or_divide_by_zero() {
        let m = BenchmarkMetrics::calculate(0, 0, 0, 0, 0);
        assert_eq!(m.elapsed_ns, 0);
        assert_eq!(m.throughput_bps, 0.0);
        assert_eq!(m.ops_per_sec, 0.0);
        assert_eq!(m.cycles_per_op, None);
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
            working_set_size: 1,
            checksum: 1,
            cpu_features: 1,
            detail: String::new(),
        }
    }

    #[test]
    fn csv_header_matches_row_column_count() {
        let result = sample_result();
        let metrics = BenchmarkMetrics::calculate(1, 1, 1, 1, 1_000_000_000);
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
        let metrics = BenchmarkMetrics::calculate(1, 1, 0, 1, 1_000_000_000);
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
        let metrics = BenchmarkMetrics::calculate(1, 1, 1, 1, 1_000_000_000);
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
        let metrics = BenchmarkMetrics::calculate(1, 1, 1, 1, 1_000_000_000);
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
