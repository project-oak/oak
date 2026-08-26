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

"""Tests for boot_latency.py.

Each case here corresponds to a way the summary could be wrong while still
printing a well-formed table, which is the failure mode that matters: a boot
latency has no independent check, so a summary that reads plausibly is the
only thing anyone will look at.
"""

import sys
import unittest

import boot_latency


def rows(*specs):
  """Builds CSV-shaped rows: (platform, iteration, ready_ms)."""
  return [
      {
          "platform": platform,
          "iteration": str(iteration),
          "ready_ns": str(int(ready_ms * 1e6)),
          "launch_ns": "250000",
          "probe_ns": "1000000",
          "attempts": "150",
      }
      for platform, iteration, ready_ms in specs
  ]


class QuantileTest(unittest.TestCase):
  """The interpolation is a hand copy of dispersion.rs and nothing enforces it.

  The expected values are those dispersion.rs produces for the same inputs:
  position = q * (n - 1), linear interpolation between the two neighbours.
  """

  def test_single_value_is_its_own_quantile(self):
    self.assertEqual(boot_latency.quantile([7], 0.25), 7.0)
    self.assertEqual(boot_latency.quantile([7], 0.75), 7.0)

  def test_three_samples_interpolate_halfway(self):
    values = [10, 20, 60]
    self.assertEqual(boot_latency.quantile(values, 0.25), 15.0)
    self.assertEqual(boot_latency.quantile(values, 0.5), 20.0)
    self.assertEqual(boot_latency.quantile(values, 0.75), 40.0)

  def test_four_samples_land_off_an_order_statistic(self):
    values = [10, 20, 30, 40]
    self.assertAlmostEqual(boot_latency.quantile(values, 0.25), 17.5)
    self.assertAlmostEqual(boot_latency.quantile(values, 0.5), 25.0)
    self.assertAlmostEqual(boot_latency.quantile(values, 0.75), 32.5)

  def test_the_top_quantile_never_runs_off_the_end(self):
    self.assertEqual(boot_latency.quantile([1, 2], 1.0), 2.0)


class SummariseTest(unittest.TestCase):

  def test_reports_the_median_not_the_mean(self):
    # A right-skewed sample: the mean is 40, the median is 20.
    stats = boot_latency.summarise([10, 20, 90])
    self.assertEqual(stats["median"], 20.0)
    self.assertEqual(stats["n"], 3)
    self.assertEqual(stats["min"], 10.0)
    self.assertEqual(stats["max"], 90.0)

  def test_does_not_assume_sorted_input(self):
    self.assertEqual(
        boot_latency.summarise([90, 10, 20]),
        boot_latency.summarise([10, 20, 90]),
    )


class FirstSampleTest(unittest.TestCase):

  def test_picks_iteration_zero_not_the_first_row(self):
    # Samples are taken round-robin, so a platform's rows arrive interleaved
    # and nothing guarantees iteration 0 is first in the file.
    oak = rows(("oak", 2, 300.0), ("oak", 0, 100.0), ("oak", 1, 200.0))
    self.assertEqual(boot_latency.first_sample(oak), 100_000_000)

  def test_absent_iteration_zero_is_not_an_error(self):
    self.assertIsNone(boot_latency.first_sample(rows(("oak", 1, 200.0))))


class RatioTest(unittest.TestCase):

  def test_ratios_are_platform_over_oak_so_above_one_is_slower(self):
    result = boot_latency.ratios({"oak": 400.0, "vm-tuned": 5200.0})
    self.assertAlmostEqual(result["vm-tuned"], 13.0)
    self.assertNotIn("oak", result)

  def test_the_untuned_row_gets_no_ratio(self):
    # Its distance from vm-tuned is one integer in one GRUB config file, so a
    # ratio against it is a ratio against a keypress timeout.
    result = boot_latency.ratios(
        {"oak": 400.0, "vm": 10400.0, "vm-tuned": 5200.0}
    )
    self.assertEqual(sorted(result), ["vm-tuned"])
    self.assertIn("vm", boot_latency.NOT_A_COMPARISON)

  def test_a_missing_baseline_yields_nothing_rather_than_dividing_by_zero(self):
    self.assertEqual(boot_latency.ratios({"vm-tuned": 5200.0}), {})
    self.assertEqual(boot_latency.ratios({"oak": 0.0, "vm-tuned": 5200.0}), {})


class ValidateTest(unittest.TestCase):

  def test_accepts_well_formed_rows(self):
    self.assertIsNone(boot_latency.validate(rows(("oak", 0, 400.0))))

  def test_rejects_a_csv_missing_a_column(self):
    bad = rows(("oak", 0, 400.0))
    del bad[0]["probe_ns"]
    self.assertIn("probe_ns", boot_latency.validate(bad))

  def test_rejects_an_empty_cell(self):
    # The driver's field() writes an empty cell when a CLI's boot-latency line
    # lacks a field, which used to surface as a traceback mid-table.
    bad = rows(("vm", 0, 400.0))
    bad[0]["ready_ns"] = ""
    complaint = boot_latency.validate(bad)
    self.assertIn("ready_ns", complaint)
    self.assertIn("vm", complaint)


if __name__ == "__main__":
  # The test runner passes flags that unittest does not know about.
  args = [arg for arg in sys.argv if not arg.startswith("--nocapture")]
  unittest.main(argv=args)
