#!/bin/bash
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
#
# Turns the benchmark VM image into a plausible serverless deployment of the
# same software, so that a boot comparison is against Linux rather than against
# a desktop image's defaults.
#
# The evaluation plan asks for "minimal Linux" as the baseline. What the
# benchmark image actually contains is the Debian nocloud image with a
# benchmark service added, and its defaults are those of an interactive
# install: a five second GRUB menu, graphical.target as the default, and the
# distribution's package-maintenance units. Measured on this host, GRUB alone
# accounts for 5.25 s of a 10.48 s time-to-ready. Reporting that as Linux boot
# latency would be reporting a keypress timeout.
#
# Nothing here is a trick played on Linux. Every change is one a cloud image
# already makes, or one any operator deploying a single-purpose appliance would
# make. The untuned image is still measured and still reported; this exists so
# that both numbers are available and the difference between them is visible.
#
# The changes are not equally worth making, and saying which is which is the
# point. Measured on this host: the GRUB timeout is worth about 5.1 s of the
# untuned 10.5 s, and it alone accounts for the whole of the systemd and menu
# tuning as well -- an image with only the timeout patched measures the same as
# one with all three applied. The kernel command line is worth a further 0.9 s.
# Hiding the menu and masking the maintenance units are defensible but, on this
# image, worth nothing measurable.
#
# GRUB's timeout variables are documented at
# <https://www.gnu.org/software/grub/manual/grub/grub.html#timeout>.

set -euo pipefail

usage() {
  cat <<EOF
Usage: $0 --input=IMAGE --output=IMAGE

Copies a qcow2 benchmark image and applies serverless-plausible boot settings:

  GRUB timeout      5 seconds, menu shown  ->  0 seconds, hidden
  default target    graphical.target       ->  multi-user.target
  masked units      unattended-upgrades, the apt maintenance timers, and
                    e2scrub_reap, none of which a single-purpose appliance runs
  kernel cmdline    drops the serial console and earlyprintk, adds quiet

Options:
  --keep-console    leave the kernel's serial console alone, so that
                    boot_phases.py can still read this image's boot

The benchmark service, the kernel, the initrd, the filesystem and every other
service are untouched.
EOF
}

INPUT=""
OUTPUT=""
KEEP_CONSOLE=false
for arg in "$@"; do
  case "${arg}" in
    --input=*) INPUT="${arg#*=}" ;;
    --output=*) OUTPUT="${arg#*=}" ;;
    --keep-console) KEEP_CONSOLE=true ;;
    --help | -h)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: ${arg}" >&2
      usage
      exit 1
      ;;
  esac
done

if [[ -z ${INPUT} || -z ${OUTPUT} ]]; then
  usage
  exit 1
fi

if ! command -v guestfish &>/dev/null; then
  echo "guestfish not found; install libguestfs-tools" >&2
  exit 1
fi

TEMP_DIR="$(mktemp -d)"
# The output is removed on any failure too: a half-patched image is worse than
# none, because it still boots and would be measured as if it were tuned.
cleanup() {
  local status=$?
  rm -rf "${TEMP_DIR}"
  if [[ ${status} -ne 0 ]]; then
    rm -f "${OUTPUT}"
  fi
}
trap cleanup EXIT

# The build writes the image read-only, and so would a previous run of this
# script, so the destination is removed rather than copied over.
rm -f "${OUTPUT}"
cp "${INPUT}" "${OUTPUT}"
chmod u+w "${OUTPUT}"

# GRUB's generated config is patched in place rather than regenerated, because
# regenerating it means running grub-mkconfig inside the guest.
guestfish -a "${OUTPUT}" -i download /boot/grub/grub.cfg "${TEMP_DIR}/grub.cfg"
sed -i \
  -e 's/^\( *\)set timeout=.*/\1set timeout=0/' \
  -e 's/^\( *\)set timeout_style=.*/\1set timeout_style=hidden/' \
  "${TEMP_DIR}/grub.cfg"

# Verified with a pattern deliberately looser than the sed's, so that a line
# the sed did not match cannot pass this check as well. An image whose timeout
# survived would be measured and reported as the tuned one, which is the number
# this whole script exists to produce.
assignments=$(grep -cE 'set[[:space:]]+timeout=' "${TEMP_DIR}/grub.cfg" || true)
if [[ ${assignments} -eq 0 ]]; then
  echo "no GRUB timeout assignment found; the config is not what we expect" >&2
  exit 1
fi

if grep -nE 'set[[:space:]]+timeout=' "${TEMP_DIR}/grub.cfg" |
  grep -vE 'set[[:space:]]+timeout=0[[:space:]]*$'; then
  echo "the GRUB timeouts above survived the patch" >&2
  exit 1
fi

# The image is built for interactive debugging: it logs the whole boot to a
# serial console and asks for early printk on the same port. The benchmark runs
# QEMU with `-serial none`, so those writes go to a UART that is not there, and
# they are on the critical path. Measured on this host, removing them is worth
# about 0.9 s of a 5.4 s boot, which is more than the two systemd changes above
# are worth put together.
#
# It is left in place under --keep-console, because boot_phases.py attributes a
# boot by reading exactly this output.
if [[ ${KEEP_CONSOLE} == false ]]; then
  # The menuentry lines are tab-indented, so the anchor has to admit any
  # whitespace. An earlier version anchored on spaces, matched nothing, and so
  # removed the consoles without adding `quiet` -- which left the kernel
  # logging at full verbosity to whatever console it fell back to, and made the
  # image 0.7 s *slower*. Both halves are checked below for that reason.
  sed -i \
    -e 's/ console=tty0//g' \
    -e 's/ console=ttyS0,[0-9]*//g' \
    -e 's/ earlyprintk=ttyS0,[0-9]*//g' \
    -e '/^[[:space:]]*linux[[:space:]]/ s/[[:space:]]*$/ quiet loglevel=0/' \
    "${TEMP_DIR}/grub.cfg"

  if grep -qE 'console=ttyS0|earlyprintk' "${TEMP_DIR}/grub.cfg"; then
    echo "a serial console setting survived the patch:" >&2
    grep -nE 'console=ttyS0|earlyprintk' "${TEMP_DIR}/grub.cfg" >&2
    exit 1
  fi

  # Removing the console without quietening the kernel is worse than doing
  # neither, so a boot entry that did not get `quiet` is a hard failure.
  if grep -nE '^[[:space:]]*linux[[:space:]]' "${TEMP_DIR}/grub.cfg" |
    grep -v 'quiet loglevel=0'; then
    echo "the boot entries above did not get a quiet kernel command line" >&2
    exit 1
  fi
fi

# Units a single-purpose appliance has no use for. Masking is a symlink to
# /dev/null in /etc/systemd/system, which systemd treats as "this unit cannot
# be started"; see systemd.unit(5).
MASKED=(
  unattended-upgrades.service
  apt-daily.service
  apt-daily.timer
  apt-daily-upgrade.service
  apt-daily-upgrade.timer
  e2scrub_reap.service
)

GF_SCRIPT="${TEMP_DIR}/guestfish_commands"
{
  echo "upload ${TEMP_DIR}/grub.cfg /boot/grub/grub.cfg"
  # The nocloud image defaults to graphical.target. On this image that costs
  # nothing measurable -- there is no display stack installed for it to pull in
  # -- but a single-purpose appliance should not be asking for one, and an
  # image that did have one would pay for it.
  echo "ln-sf /lib/systemd/system/multi-user.target /etc/systemd/system/default.target"
  for unit in "${MASKED[@]}"; do
    echo "ln-sf /dev/null /etc/systemd/system/${unit}"
  done
} >"${GF_SCRIPT}"

guestfish -a "${OUTPUT}" -i <"${GF_SCRIPT}"

echo "wrote ${OUTPUT}"
