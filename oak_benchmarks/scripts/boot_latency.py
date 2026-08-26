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

"""Summarises the CSV that boot_latency.sh writes.

Reports a median with quartiles rather than a mean, matching the rest of the
suite: a boot latency is one draw from a right-skewed distribution and its mean
is dragged around by the tail.

The first sample of each platform is reported separately as well as included.
No sample runs against a cold host page cache -- the build writes every image
immediately beforehand and dropping the cache needs root -- so this column is
not a cold-start figure. It is here so that a reader can see whether there is
a first-sample effect at all, which on a warm host there should not be.

Platforms are not hardcoded: whatever appears in the CSV is summarised, and
every platform other than `oak` is also expressed as a ratio against it.
"""

import argparse
import csv
import sys

# Without these the summary would either crash halfway through printing or
# quietly describe something other than what was measured.
REQUIRED_COLUMNS = frozenset(
    ["platform", "iteration", "ready_ns", "probe_ns", "attempts"]
)

# Platforms that are measured for context and must not be turned into a ratio.
# `vm` is the benchmark image with its defaults, and an image with only its
# bootloader timeout patched measures the same as the fully tuned one, so the
# distance between `vm` and `vm-tuned` is one integer in one config file. A
# ratio against it would be a ratio against `sleep 5`, and a ratio that is
# printed is a ratio that gets quoted.
NOT_A_COMPARISON = {
    "vm": (
        "the image's own defaults; about half of it is a bootloader menu"
        " waiting for a keypress. Use vm-tuned for any comparison."
    )
}

# Below this many samples an interquartile range is not a description of a
# distribution: at n=3 it is just (min+median)/2 and (median+max)/2.
MIN_SAMPLES_FOR_QUARTILES = 8


def quantile(sorted_values, q):
  """Linear interpolation between order statistics, as in dispersion.rs."""
  if not sorted_values:
    return 0.0
  if len(sorted_values) == 1:
    return float(sorted_values[0])
  position = q * (len(sorted_values) - 1)
  low = int(position)
  high = min(low + 1, len(sorted_values) - 1)
  weight = position - low
  return sorted_values[low] * (1.0 - weight) + sorted_values[high] * weight


def summarise(values):
  ordered = sorted(values)
  return {
      "n": len(ordered),
      "min": float(ordered[0]),
      "q1": quantile(ordered, 0.25),
      "median": quantile(ordered, 0.5),
      "q3": quantile(ordered, 0.75),
      "max": float(ordered[-1]),
  }


def ms(nanoseconds):
  return nanoseconds / 1e6


def validate(rows):
  """Returns a complaint about the rows, or None if they can be summarised."""
  missing = REQUIRED_COLUMNS - set(rows[0])
  if missing:
    return f"missing columns: {', '.join(sorted(missing))}"
  # The driver writes an empty cell if a CLI's boot-latency line lacked a
  # field, which would otherwise surface as a traceback halfway through the
  # table.
  for row in rows:
    for column in sorted(REQUIRED_COLUMNS - {"platform"}):
      if not row[column].strip().isdigit():
        return f"{row['platform']} has a non-numeric {column}: {row[column]!r}"
  return None


def first_sample(platform_rows):
  """The ready time of iteration 0, or None if this platform has no such row.

  Selected by iteration rather than by position: samples are taken round-robin,
  so a platform's rows are not contiguous in the file and the first row of a
  platform is not necessarily its first sample.
  """
  return next(
      (int(r["ready_ns"]) for r in platform_rows if int(r["iteration"]) == 0),
      None,
  )


def ratios(medians, baseline="oak"):
  """Every comparable platform's median over the baseline's.

  Above one means the platform is slower than the baseline. Platforms listed in
  NOT_A_COMPARISON are left out rather than reported with a caveat, because a
  printed ratio outlives the paragraph next to it.
  """
  if medians.get(baseline, 0) <= 0:
    return {}
  return {
      platform: value / medians[baseline]
      for platform, value in sorted(medians.items())
      if platform != baseline and platform not in NOT_A_COMPARISON
  }


def main():
  parser = argparse.ArgumentParser(
      description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
  )
  parser.add_argument("--csv", required=True, help="boot_latency.csv to read")
  args = parser.parse_args()

  try:
    with open(args.csv, newline="") as f:
      rows = list(csv.DictReader(f))
  except OSError as e:
    print(f"reading {args.csv}: {e}", file=sys.stderr)
    return 2

  if not rows:
    print(f"{args.csv}: no data rows", file=sys.stderr)
    return 2

  complaint = validate(rows)
  if complaint:
    print(f"{args.csv}: {complaint}", file=sys.stderr)
    return 2

  by_platform = {}
  for row in rows:
    by_platform.setdefault(row["platform"], []).append(row)

  print(
      f"{'platform':10} {'n':>3} {'median':>10} {'q1':>10} {'q3':>10} "
      f"{'min':>10} {'max':>10} {'first':>10}"
  )
  print(
      f"{'':10} {'':>3} {'ms':>10} {'ms':>10} {'ms':>10} "
      f"{'ms':>10} {'ms':>10} {'ms':>10}"
  )

  medians = {}
  for platform, platform_rows in by_platform.items():
    ready = [int(r["ready_ns"]) for r in platform_rows]
    stats = summarise(ready)
    medians[platform] = stats["median"]
    first = first_sample(platform_rows)
    first_column = "--" if first is None else f"{ms(first):.1f}"
    if stats["n"] >= MIN_SAMPLES_FOR_QUARTILES:
      q1 = f"{ms(stats['q1']):.1f}"
      q3 = f"{ms(stats['q3']):.1f}"
    else:
      q1 = q3 = "--"
    print(
        f"{platform:10} {stats['n']:>3} {ms(stats['median']):>10.1f}"
        f" {q1:>10} {q3:>10}"
        f" {ms(stats['min']):>10.1f} {ms(stats['max']):>10.1f}"
        f" {first_column:>10}"
    )

  # How the readiness of each platform was established. `probe_ns` bounds the
  # error: the guest was reachable at most that long before the probe that
  # found it returned. A platform with no readiness loop reports zero for
  # both, which is not the same as one probe.
  print()
  for platform, platform_rows in by_platform.items():
    probe = max(int(r["probe_ns"]) for r in platform_rows)
    attempts = max(int(r["attempts"]) for r in platform_rows)
    if attempts == 0:
      print(
          f"{platform}: no readiness loop; the first response is the launch's"
      )
    else:
      print(
          f"{platform}: at most {attempts} readiness probes, the successful one"
          f" taking at most {ms(probe):.1f} ms"
      )

  # Every Linux row is expressed against the enclave, because that ratio is
  # the claim. Reporting only the untuned one would credit the enclave with a
  # bootloader menu timeout.
  against_oak = ratios(medians)
  if against_oak:
    print()
    for platform, ratio in against_oak.items():
      print(f"{platform} / oak at the median: {ratio:.1f}x")

  for platform, reason in sorted(NOT_A_COMPARISON.items()):
    if platform in medians:
      print(f"{platform}: no ratio reported. {reason}")

  if any(
      len(rows) < MIN_SAMPLES_FOR_QUARTILES for rows in by_platform.values()
  ):
    print()
    print(
        f"quartiles need at least {MIN_SAMPLES_FOR_QUARTILES} samples to"
        " describe anything, and a P99 needs about a hundred"
    )

  return 0


if __name__ == "__main__":
  sys.exit(main())
