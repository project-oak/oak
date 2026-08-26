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

"""Attributes a Linux guest's boot time to its phases, from the host's clock.

boot_latency.sh reports one number per launch. That number is only worth
quoting once somebody has checked what is inside it, and on the untuned
benchmark image slightly more than half of it turned out to be a GRUB menu
waiting for a keypress.

This watches the guest's serial console and records, against the host's
monotonic clock, when each phase first announces itself. The phases are read
off the console rather than out of the guest's own clock so that they sit on
the same timeline as the boot measurement, and so that the interval before the
kernel starts counting is visible at all.

This is a diagnostic, not the measurement. Serial output is itself work the
guest would not otherwise do, so the total here runs longer than what
boot_latency.sh reports, and the two should not be mixed in a table.

The bootloader row is the one to distrust, and not simply because it is
inflated. GRUB drives the serial terminal at 115200 baud, and where that cost
shows up depends on whether its menu is displayed. On the untuned image the
console work overlaps the five second menu countdown and is absorbed by it; on
an image whose timeout is zero there is nothing to hide behind, so this tool
attributes 3.1 s to a bootloader that the benchmark, running the same image
with no console at all, gets through in a fraction of that. Differences between
two rows of this table are only meaningful when both were measured in this
mode.
"""

import argparse
import os
import re
import signal
import subprocess
import sys
import threading
import time

# Ordered, and matched in order: each marker is only looked for once the
# previous one has been seen, so that a string appearing in an earlier phase
# cannot be mistaken for a later one.
MARKERS = [
    ("GRUB loading", "firmware handed off to GRUB"),
    ("Loading Linux", "GRUB handed off to the kernel"),
    ("systemd[1]", "init started"),
    ("Started app.service", "benchmark service started"),
]

# Strips the ANSI colour systemd writes to the console, which would otherwise
# break a match on a line's text.
ANSI = re.compile(r"\x1b\[[0-9;?]*[a-zA-Z]")


def main():
  parser = argparse.ArgumentParser(
      description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
  )
  parser.add_argument("--image", required=True, help="qcow2 image to boot")
  parser.add_argument(
      "--run-vm-script",
      default="oak_benchmarks/linux_vm/run_vm.sh",
      help="the script that knows how to invoke QEMU",
  )
  parser.add_argument(
      "--port", type=int, default=5057, help="forwarded guest port"
  )
  parser.add_argument("--memory", default="1G", help="guest memory")
  parser.add_argument("--cpus", type=int, default=1, help="guest vCPUs")
  parser.add_argument(
      "--timeout",
      type=float,
      default=60.0,
      help="give up after this many seconds",
  )
  args = parser.parse_args()

  command = [
      args.run_vm_script,
      f"--image={args.image}",
      f"--port={args.port}",
      f"--memory={args.memory}",
      f"--cpus={args.cpus}",
  ]

  start = time.monotonic()
  # A process group, so that killing the wrapper takes QEMU with it: run_vm.sh
  # execs QEMU, but the shell may still be between the two when we give up.
  process = subprocess.Popen(
      command,
      stdin=subprocess.DEVNULL,
      stdout=subprocess.PIPE,
      stderr=subprocess.STDOUT,
      text=True,
      errors="replace",
      start_new_session=True,
  )

  # The deadline is enforced by a timer rather than by the loop below, because
  # a guest that stops writing to the console leaves readline() blocked and the
  # loop's own check unreachable. Killing the group unblocks it.
  watchdog = threading.Timer(
      args.timeout, lambda: os.killpg(process.pid, signal.SIGKILL)
  )
  watchdog.daemon = True
  watchdog.start()

  pending = list(MARKERS)
  found = []
  try:
    while pending and time.monotonic() - start < args.timeout:
      line = process.stdout.readline()
      if not line:
        break
      line = ANSI.sub("", line)
      if pending[0][0] in line:
        found.append((time.monotonic() - start, pending[0][1]))
        pending.pop(0)
  finally:
    watchdog.cancel()
    os.killpg(process.pid, signal.SIGTERM)
    try:
      process.wait(timeout=10)
    except subprocess.TimeoutExpired:
      os.killpg(process.pid, signal.SIGKILL)

  if not found:
    print("no boot markers seen; is this a Linux image?", file=sys.stderr)
    return 1

  print(f"{'at':>10}  {'phase took':>10}  event")
  print(f"{'ms':>10}  {'ms':>10}")
  previous = 0.0
  for at, label in found:
    print(f"{at * 1000:>10.0f}  {(at - previous) * 1000:>10.0f}  {label}")
    previous = at

  for _, label in pending:
    print(f"{'--':>10}  {'--':>10}  {label} (not seen)")

  print()
  print(
      "these phases are read off a serial console that the benchmark does not"
  )
  print(
      "enable, which inflates them, the bootloader row most of all. Attribute"
  )
  print("with these numbers; quote boot_latency.sh's.")

  return 0 if not pending else 1


if __name__ == "__main__":
  sys.exit(main())
