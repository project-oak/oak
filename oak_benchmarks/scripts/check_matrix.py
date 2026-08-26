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

"""Checks that the CSVs a matrix run produced are comparable to each other.

`run_matrix.sh` writes one CSV per platform. Nothing in that output says
whether the rows may be placed side by side: two platforms can complete the
same benchmark and still have been asked for different work, or have run
different code. This refuses the comparison when they did.

What is checked, across every platform that ran:

  shape          at least two platforms, the same set of benchmarks in each,
                 and the same number of repetitions per benchmark. Without
                 these the remaining checks are vacuous rather than passing
  parameters     `iterations`, `data_size` and `working_set_size` agree per
                 benchmark, and are constant across a platform's repetitions
  status         per benchmark. A non-zero status means the row is an error
                 report, not a measurement. Note that `run_matrix.sh` cannot
                 produce such a row: both CLIs validate the status before
                 printing anything, so a failing benchmark aborts the matrix
                 instead. The check is here for CSVs assembled by hand
  checksum       per benchmark. The runs computed the same answer
  cpu_features   once for the whole run. The compile-time set, the CPUID set
                 and the runtime-dispatch flag are compared separately, so a
                 pair that reaches the same instructions by different routes
                 is still reported

The `cpu_features` check is the one the suite used to print and never act on.
`cpu/mod.rs` states the criterion -- "if two runs report the same effective set,
they used the same implementations" -- but the value only ever reached a column.
The enclave build reaches neither SHA-NI nor AVX-512, because `cpufeatures`
compiles its runtime detection out under `target_os = "none"` and
`ENCLAVE_TARGET_FEATURES` does not ask for them. All three platforms compile
against that same feature list, so on a host whose `CPUID` reports SHA-NI and
AVX-512 IFMA the two Linux platforms reach them by dispatch and the enclave
does not. On a host without them the three agree and this check passes; the
outcome depends on the machine, not only on the build.

The `vm` platform matches `native` only because `linux_vm/run_vm.sh` passes
`-cpu host`. Without it the guest sees a QEMU CPU model and this check fails
vm-against-native for a reason that has nothing to do with either kernel.

Two limits worth stating, because a green verdict does not cover them.

Three benchmarks match across platforms for free, so their agreement is not
evidence of anything; they are named in the output rather than silently
counted. See the README's "Making a Comparison Valid".

And `cpu_features` describes the dispatch-capable crypto crates, not codegen.
`cpu/mod.rs` says so directly: a crate like `p256` emits whatever the
compile-time features permit, so two builds given different `-C target-cpu` can
differ while reporting the same bits. That divergence is invisible here; the
baseline's Bazel build transition is what closes it.

Exit status is 0 when every check passes, 1 when any fails, and 2 when the
inputs could not be read.
"""

import argparse
import csv
import os
import sys

# Mirrors `CpuFeatures::to_wire` in oak_benchmarks/benchmark/cpu/mod.rs: bits
# 0-7 are the compile-time set, bits 8-15 the CPUID set, bit 16 the
# runtime-dispatch flag. Kept in sync by hand.
FEATURE_NAMES = [
    "SHA_NI",
    "AES_NI",
    "PCLMULQDQ",
    "AVX2",
    "AVX512IFMA",
    "AVX512VL",
]
FEATURE_MASK = (1 << len(FEATURE_NAMES)) - 1
RUNTIME_DISPATCH_BIT = 1 << 16

PLATFORM_FILES = [
    ("native", "native.csv"),
    ("vm", "vm.csv"),
    ("oak", "oak.csv"),
]

# Columns that describe what was asked for rather than what happened. Two rows
# whose checksums agree are still not comparable if these differ, and for
# `alloc-churn` that is not hypothetical: its checksum is the same at a 64-byte
# allocation as at a 1 MiB one.
PARAMETER_COLUMNS = ["iterations", "data_size", "working_set_size"]

# Benchmarks whose checksums agree across platforms by construction, keyed by
# the `display_name` the CSV carries (see `BENCHMARKS` in cli_common/cli.rs).
# Their agreement is reported, not counted.
FREE_MATCHING = {
    "Alloc Churn": (
        "takes no seed and folds a closed form in the iteration count"
    ),
    "Null Syscall": "folds a count the run forces to equal --iterations",
    "Syscall Control (no syscall)": (
        "folds a count the run forces to equal --iterations"
    ),
}


def effective_features(wire):
  """Returns the feature bits the crypto backends could actually reach."""
  compiled = wire & FEATURE_MASK
  available = (wire >> 8) & FEATURE_MASK
  if wire & RUNTIME_DISPATCH_BIT:
    return compiled | available
  return compiled


def format_features(bits):
  names = [n for i, n in enumerate(FEATURE_NAMES) if bits & (1 << i)]
  return " | ".join(names) if names else "none"


def describe_wire(wire):
  """Renders the three halves of a `cpu_features` value separately."""
  return (
      f"compiled={format_features(wire & FEATURE_MASK)}"
      f", cpuid={format_features((wire >> 8) & FEATURE_MASK)}"
      f", runtime_dispatch={bool(wire & RUNTIME_DISPATCH_BIT)}"
      f", effective={format_features(effective_features(wire))}"
  )


# Columns every check below reads. Validated up front so that a CSV written by
# an older binary fails as a bad input rather than as a failed comparison.
REQUIRED_COLUMNS = [
    "benchmark",
    "checksum",
    "cpu_features",
    "status",
] + PARAMETER_COLUMNS


def read_platform(path):
  """Returns {benchmark: [row, ...]} for one platform's CSV."""
  with open(path, newline="") as f:
    rows = list(csv.DictReader(f))
  if not rows:
    raise ValueError(f"{path}: no data rows")
  missing = [c for c in REQUIRED_COLUMNS if c not in rows[0]]
  if missing:
    raise ValueError(f"{path}: missing columns {missing}")
  by_benchmark = {}
  for row in rows:
    by_benchmark.setdefault(row["benchmark"], []).append(row)
  return by_benchmark


def distinct(values):
  """Returns the distinct values in first-seen order."""
  seen = []
  for v in values:
    if v not in seen:
      seen.append(v)
  return seen


def check_shape(platforms):
  """Rejects a comparison that would have nothing to compare.

  A single platform, a benchmark only one platform ran, or an unequal number
  of repetitions all let the later checks pass while examining less than the
  reader will assume they examined. Deleting the rows that disagreed would
  otherwise be indistinguishable from agreement.
  """
  failures = 0
  if len(platforms) < 2:
    got = ", ".join(platforms) if platforms else "none"
    print(f"only one platform to compare ({got}); nothing to check")
    return 1

  names = {p: set(rows) for p, rows in platforms.items()}
  everything = set.union(*names.values())
  for platform, own in names.items():
    missing = everything - own
    if missing:
      print(
          f"{platform}: missing benchmarks other platforms ran:"
          f" {sorted(missing)}"
      )
      failures += 1

  for name in sorted(set.intersection(*names.values())):
    counts = {p: len(platforms[p][name]) for p in platforms}
    if len(set(counts.values())) > 1:
      detail = ", ".join(f"{p}={c}" for p, c in counts.items())
      print(f"{name}: repetition counts differ across platforms: {detail}")
      failures += 1

  return failures


def check_parameters(platforms, name):
  """Compares what each platform was asked to do, not what it measured."""
  failures = 0
  for column in PARAMETER_COLUMNS:
    values = {}
    for platform, by_benchmark in platforms.items():
      own = distinct(r[column] for r in by_benchmark[name])
      if len(own) > 1:
        print(f"{name}: {platform} varied {column} between repetitions: {own}")
        failures += 1
      values[platform] = own[0]
    if len(set(values.values())) > 1:
      detail = ", ".join(f"{p}={v}" for p, v in values.items())
      print(f"{name}: {column} differs across platforms: {detail}")
      failures += 1
  return failures


def check_benchmarks(platforms):
  """Reports every per-benchmark disagreement; returns the number found."""
  failures = 0
  shared = sorted(set.intersection(*[set(rows) for rows in platforms.values()]))

  for name in shared:
    for platform, by_benchmark in platforms.items():
      rows = by_benchmark[name]
      bad = [r for r in rows if r["status"] != "0"]
      if bad:
        print(
            f"{name}: {platform} reported status {bad[0]['status']} "
            f"in {len(bad)} of {len(rows)} repetitions"
        )
        failures += 1

    failures += check_parameters(platforms, name)

    checksums = {}
    for platform, by_benchmark in platforms.items():
      own = distinct(r["checksum"] for r in by_benchmark[name])
      if len(own) > 1:
        print(f"{name}: {platform} changed checksum between repetitions: {own}")
        failures += 1
      checksums[platform] = own[0]
    if len(set(checksums.values())) > 1:
      detail = ", ".join(f"{p}={v}" for p, v in checksums.items())
      print(f"{name}: checksums disagree across platforms: {detail}")
      failures += 1

  return failures


def check_features(platforms):
  """Compares the reachable instruction set across platforms.

  The value is a property of the build and the machine, not of an individual
  benchmark, so a divergence is reported once rather than once per row. Every
  row is read, because a platform whose CSV was assembled from more than one
  binary would otherwise hide behind whichever benchmark came first.
  """
  failures = 0
  wires = {}
  for platform, by_benchmark in platforms.items():
    own = distinct(
        int(r["cpu_features"]) for rows in by_benchmark.values() for r in rows
    )
    if len(own) > 1:
      print(f"{platform}: cpu_features changed within the run:")
      for wire in own:
        print(f"  {describe_wire(wire)}")
      failures += 1
    wires[platform] = own[0]

  if len(set(wires.values())) > 1:
    print("cpu_features disagree across platforms:")
    for platform, wire in wires.items():
      print(f"  {platform}: {describe_wire(wire)}")
    print(
        "  rows from these platforms are not comparable: the crypto "
        "backends could reach different instructions"
    )
    failures += 1

  return failures


def report_free_matching(platforms):
  """Names the rows whose agreement above was guaranteed in advance."""
  shared = set.intersection(*[set(rows) for rows in platforms.values()])
  exempt = sorted(shared & set(FREE_MATCHING))
  if not exempt:
    return
  print("\nchecksum agreement is not evidence for:")
  for name in exempt:
    print(f"  {name}: {FREE_MATCHING[name]}")


def main():
  parser = argparse.ArgumentParser(
      description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
  )
  parser.add_argument(
      "--dir",
      required=True,
      help="directory holding the CSVs run_matrix.sh wrote",
  )
  parser.add_argument(
      "--platforms",
      default="",
      help=(
          "platforms the run was supposed to produce, space or comma separated."
          " A CSV that is expected and absent is an error rather than a"
          " platform quietly left out of the comparison"
      ),
  )
  args = parser.parse_args()

  known = dict(PLATFORM_FILES)
  expected = args.platforms.replace(",", " ").split()
  unknown = [p for p in expected if p not in known]
  if unknown:
    print(f"unknown platform(s): {unknown}", file=sys.stderr)
    return 2

  platforms = {}
  for platform, filename in PLATFORM_FILES:
    path = os.path.join(args.dir, filename)
    if not os.path.exists(path):
      if platform in expected:
        print(f"expected {path} and it is not there", file=sys.stderr)
        return 2
      continue
    try:
      platforms[platform] = read_platform(path)
    except (OSError, ValueError, KeyError) as e:
      print(f"reading {path}: {e}", file=sys.stderr)
      return 2

  if not platforms:
    print(f"no platform CSVs found under {args.dir}", file=sys.stderr)
    return 2

  failures = check_shape(platforms)
  if failures:
    print(f"\n{failures} check(s) failed; the later checks were not run")
    return 1

  failures = check_benchmarks(platforms) + check_features(platforms)
  if failures:
    print(f"\n{failures} check(s) failed across {', '.join(platforms)}")
    return 1

  print(f"checks passed across {', '.join(platforms)}")
  report_free_matching(platforms)
  return 0


if __name__ == "__main__":
  sys.exit(main())
