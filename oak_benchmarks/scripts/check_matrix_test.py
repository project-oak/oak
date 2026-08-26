#!/usr/bin/env python3
#
# Copyright 2026 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Tests for check_matrix.

A gate is only worth what it rejects, so most of these are attempts to slip an
incomparable pair of runs past it. Each one passed an earlier version.
"""

import os
import sys
import tempfile
import unittest

import check_matrix

# One row's worth of columns, in the order `repeated_csv_header` emits them.
HEADER = (
    "repetition,benchmark,data_size,iterations,elapsed_tsc,elapsed_ns,"
    "bytes_processed,byte_semantics,throughput_bps,ops_per_sec,tsc_ticks_per_op,"
    "ns_per_op,tsc_ticks_per_byte,working_set_size,checksum,cpu_features,detail,status"
)

# Both Linux platforms report this: everything compiled, everything in CPUID,
# runtime dispatch on.
LINUX_FEATURES = 0x1003F
# The enclave: AES-NI, PCLMULQDQ and AVX2 compiled, no dispatch.
ENCLAVE_FEATURES = 0x0000E


def row(
    benchmark="SHA-256",
    repetition=0,
    data_size=1024,
    iterations=2000,
    working_set_size=0,
    checksum=42,
    cpu_features=LINUX_FEATURES,
    status=0,
):
  return (
      f"{repetition},{benchmark},{data_size},{iterations},100,100,1024,message,"
      f"1,1,1.0,1.0,1.0,{working_set_size},{checksum},{cpu_features},,{status}"
  )


class CheckMatrixTest(unittest.TestCase):

  def run_check(self, platforms, expected_platforms=""):
    """Writes one CSV per platform and returns check_matrix's exit status."""
    with tempfile.TemporaryDirectory() as d:
      for name, rows in platforms.items():
        with open(os.path.join(d, f"{name}.csv"), "w") as f:
          f.write("\n".join([HEADER] + rows) + "\n")
      argv = ["check_matrix", f"--dir={d}"]
      if expected_platforms:
        argv.append(f"--platforms={expected_platforms}")
      old = sys.argv
      sys.argv = argv
      try:
        return check_matrix.main()
      finally:
        sys.argv = old

  def test_matching_runs_pass(self):
    self.assertEqual(
        self.run_check({"native": [row()], "oak": [row()]}),
        0,
    )

  def test_differing_checksums_fail(self):
    self.assertEqual(
        self.run_check({"native": [row()], "oak": [row(checksum=43)]}),
        1,
    )

  def test_checksum_unstable_within_a_platform_fails(self):
    self.assertEqual(
        self.run_check({
            "native": [row(), row(repetition=1)],
            "oak": [row(), row(repetition=1, checksum=43)],
        }),
        1,
    )

  def test_differing_features_fail(self):
    self.assertEqual(
        self.run_check(
            {"native": [row()], "oak": [row(cpu_features=ENCLAVE_FEATURES)]}
        ),
        1,
    )

  def test_features_differing_only_in_dispatch_fail(self):
    # Same effective set by two different routes: one compiled it in, the
    # other dispatches to it. Comparing only `effective` would pass this.
    self.assertEqual(
        self.run_check({
            "native": [row(cpu_features=0x1000E)],
            "oak": [row(cpu_features=0x0000E)],
        }),
        1,
    )

  def test_non_zero_status_fails(self):
    self.assertEqual(
        self.run_check({"native": [row()], "oak": [row(status=4)]}),
        1,
    )

  def test_differing_iterations_fail(self):
    self.assertEqual(
        self.run_check({"native": [row()], "oak": [row(iterations=100)]}),
        1,
    )

  def test_differing_data_size_fails(self):
    # alloc-churn's checksum is the same at 64 bytes as at 1 MiB, so the
    # parameter column is the only thing that catches this.
    self.assertEqual(
        self.run_check({
            "native": [row(benchmark="Alloc Churn", data_size=64)],
            "oak": [row(benchmark="Alloc Churn", data_size=1048576)],
        }),
        1,
    )

  def test_differing_working_set_fails(self):
    self.assertEqual(
        self.run_check(
            {"native": [row()], "oak": [row(working_set_size=268435456)]}
        ),
        1,
    )

  def test_unequal_repetition_counts_fail(self):
    self.assertEqual(
        self.run_check({
            "native": [row(), row(repetition=1)],
            "oak": [row()],
        }),
        1,
    )

  def test_a_benchmark_missing_from_one_platform_fails(self):
    self.assertEqual(
        self.run_check({
            "native": [row(), row(benchmark="SHA-512")],
            "oak": [row()],
        }),
        1,
    )

  def test_a_single_platform_fails(self):
    self.assertEqual(self.run_check({"oak": [row()]}), 1)

  def test_an_expected_platform_that_is_absent_fails(self):
    self.assertEqual(
        self.run_check(
            {"native": [row()], "oak": [row()]},
            expected_platforms="native oak vm",
        ),
        2,
    )

  def test_a_missing_column_is_a_bad_input(self):
    with tempfile.TemporaryDirectory() as d:
      for name in ("native", "oak"):
        with open(os.path.join(d, f"{name}.csv"), "w") as f:
          f.write("benchmark,checksum\nSHA-256,42\n")
      sys.argv = ["check_matrix", f"--dir={d}"]
      self.assertEqual(check_matrix.main(), 2)

  def test_the_free_matching_rows_are_named(self):
    # They still pass; the point is that the reader is told their agreement
    # was guaranteed in advance.
    self.assertEqual(
        self.run_check({
            "native": [row(benchmark="Null Syscall")],
            "oak": [row(benchmark="Null Syscall")],
        }),
        0,
    )
    self.assertIn("Null Syscall", check_matrix.FREE_MATCHING)


if __name__ == "__main__":
  args = [arg for arg in sys.argv if not arg.startswith("--nocapture")]
  unittest.main(argv=args)
