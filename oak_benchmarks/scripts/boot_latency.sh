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
# Measures cold-boot latency: how long a caller waits between asking for an
# enclave and getting an answer out of it.
#
# Every sample is a fresh process that launches a fresh guest, because the
# quantity being measured only exists once per launch. This is the one
# benchmark in the suite where repeating inside a single process would measure
# nothing at all.
#
# The clock starts inside each CLI, immediately before the VMM is spawned, and
# stops when the guest answers a `debug` request, which does no work in the
# guest. Both platforms use that same definition; see the
# --report-boot-latency documentation on either CLI.
#
# On Linux the clock starts before a shell script is spawned and that script
# goes on to exec QEMU, so a few milliseconds of the Linux figure are the
# wrapper rather than the guest.
#
# Linux is measured twice, because the benchmark image is a desktop Debian
# install and most of its boot is settings rather than Linux:
#
#   vm         the image exactly as the build produces it
#   vm-tuned   the same image with the settings a serverless deployment would
#              already have changed, applied by tune_vm_image.sh
#
# Both are reported. The evaluation plan asks for minimal Linux, so `vm-tuned`
# is the comparison, and `vm` is what says how much of the difference was ever
# about the kernel.

set -euo pipefail

CORES="${CORES:-6,7}"
ITERATIONS="${ITERATIONS:-10}"
MEMORY="${MEMORY:-1024M}"
PLATFORMS="${PLATFORMS:-oak vm vm-tuned}"
PROBE_TIMEOUT_MS="${PROBE_TIMEOUT_MS:-100}"
POLL_INTERVAL_MS="${POLL_INTERVAL_MS:-5}"
OUT_DIR="${OUT_DIR:-/tmp/oak_boot_$(date +%Y%m%d_%H%M%S)}"

usage() {
  cat <<EOF
Usage: $0 [--help]

Environment variables:
  CORES=6,7               Logical CPUs to pin every launch to
  ITERATIONS=10           Cold boots per platform
  MEMORY=1024M            Guest memory
  PLATFORMS=...           Which platforms to measure, from oak, vm, vm-tuned
  PROBE_TIMEOUT_MS=100    Bound on how long one readiness probe may block
  POLL_INTERVAL_MS=5      Gap between readiness probes
  OUT_DIR=<path>          Where to write the CSV and the manifest

Writes boot_latency.csv and manifest.txt, then summarises with
boot_latency.py.
EOF
}

if [[ ${1:-} == "--help" || ${1:-} == "-h" ]]; then
  usage
  exit 0
fi

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${REPO_ROOT}"

mkdir -p "${OUT_DIR}"
rm -f "${OUT_DIR}"/*.csv "${OUT_DIR}"/*.log

BAZEL=(direnv exec "${REPO_ROOT}" bazel)
PIN=(taskset -c "${CORES}")
CSV="${OUT_DIR}/boot_latency.csv"
BUILT_IMAGE="${REPO_ROOT}/bazel-bin/oak_benchmarks/linux_enclave_app/linux_enclave_image.qcow2"
RUN_VM_SCRIPT="${REPO_ROOT}/oak_benchmarks/linux_vm/run_vm.sh"

# Both Linux rows read their image from here and are launched by the same
# command, so that the only difference between them is the tuning. They used to
# differ in launch path and in filesystem as well, which made the comparison
# two-variable: OUT_DIR defaults under /tmp, which is tmpfs on some hosts,
# while bazel-bin is on disk.
declare -A IMAGE=(
  [vm]="${OUT_DIR}/linux_untuned.qcow2"
  [vm-tuned]="${OUT_DIR}/linux_tuned.qcow2"
)

# QEMU and guestfish come from the nix shell, so anything that spawns them has
# to be inside one. `bazel run` already is; a bare binary is not.
SHELL_ENV=(direnv exec "${REPO_ROOT}")

# The trivial workload. `debug` exists to have a benchmark that does nothing,
# which is what a boot measurement wants inside its window.
WORKLOAD=(--benchmark=debug --iterations=1 --warmup-iterations=0)

# Extracts one field from the `boot-latency` line the CLIs print.
field() {
  sed -n "s/.*\\b$2=\\([0-9]*\\).*/\\1/p" <<<"$1"
}

# Builds first, so that no sample pays for a compile. A build inside the timed
# region would land entirely on whichever platform ran first.
prebuild() {
  echo "building..." >&2
  for p in ${PLATFORMS}; do
    case "${p}" in
      oak) "${BAZEL[@]}" build -c opt //oak_benchmarks/oak_enclave_app:oak_enclave_app_run ;;
      vm)
        "${BAZEL[@]}" build -c opt \
          //oak_benchmarks/linux_cli \
          //oak_benchmarks/linux_enclave_app:linux_enclave_image
        rm -f "${IMAGE[vm]}"
        cp "${BUILT_IMAGE}" "${IMAGE[vm]}"
        chmod u+w "${IMAGE[vm]}"
        ;;
      vm-tuned)
        "${BAZEL[@]}" build -c opt \
          //oak_benchmarks/linux_cli \
          //oak_benchmarks/linux_enclave_app:linux_enclave_image
        # Derived once, before any sample, so no launch pays for it and every
        # sample of this platform uses the same bytes.
        "${SHELL_ENV[@]}" "${REPO_ROOT}/oak_benchmarks/scripts/tune_vm_image.sh" \
          --input="${BUILT_IMAGE}" \
          --output="${IMAGE[vm-tuned]}"
        ;;
      *)
        echo "unknown platform: ${p}" >&2
        exit 1
        ;;
    esac
  done >&2
}

write_manifest() {
  local f="${OUT_DIR}/manifest.txt"
  {
    echo "date: $(date -Is)"
    echo "host: $(uname -n), kernel $(uname -r)"
    echo "cpu: $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ //')"
    echo "pinned to logical CPUs: ${CORES}"
    echo "loadavg at start: $(cut -d' ' -f1-3 /proc/loadavg)"
    echo "iterations per platform: ${ITERATIONS}"
    echo "guest memory: ${MEMORY}"
    echo "probe timeout: ${PROBE_TIMEOUT_MS} ms"
    echo "poll interval: ${POLL_INTERVAL_MS} ms"
    echo "platforms, sampled round-robin: ${PLATFORMS}"
    echo "guest vCPUs: 1"
    echo "workload: ${WORKLOAD[*]}"
    # Inside the nix shell, or the VMM this whole benchmark measures goes
    # unrecorded.
    echo "qemu: $("${SHELL_ENV[@]}" qemu-system-x86_64 --version 2>/dev/null |
      head -1 || echo unknown)"
    # Without --ignore-working-copy, so that uncommitted changes show up as a
    # different commit rather than being silently attributed to the last one.
    echo "revision: $(jj log -r @ --no-graph -T 'commit_id' 2>/dev/null || echo unknown)"
    for p in ${PLATFORMS}; do
      if [[ -n ${IMAGE[${p}]:-} ]]; then
        echo "${p} image: $(sha256sum "${IMAGE[${p}]}" | cut -c1-16)"
      fi
    done
    echo
    echo "not controlled:"
    echo "  no sample runs against a cold host page cache. The build writes"
    echo "  every image and kernel immediately beforehand, and dropping the"
    echo "  cache needs root, which is not available here. The summary reports"
    echo "  the first sample separately so that a reader can see whether there"
    echo "  is a first-sample effect; on this host there is none."
    echo "  the SMT siblings of the pinned CPUs are not in the mask but are"
    echo "  still schedulable by the rest of the machine."
    echo "  the host was not otherwise idle; see loadavg above"
  } >"${f}"
  echo "wrote ${f}"
}

# One cold boot of one platform, appended to the CSV.
take_sample() {
  local platform="$1" i="$2"
  local log="${OUT_DIR}/${platform}.log"
  local line=""

  case "${platform}" in
    oak)
      line=$("${PIN[@]}" "${BAZEL[@]}" run -c opt \
        //oak_benchmarks/oak_enclave_app:oak_enclave_app_run -- \
        --memory-size="${MEMORY}" "${WORKLOAD[@]}" --report-boot-latency \
        2>>"${log}" | grep '^boot-latency ') || true
      ;;
    vm | vm-tuned)
      # Both rows run the same binary against images in the same directory, so
      # the tuning is the only thing that differs between them.
      line=$("${PIN[@]}" "${BAZEL[@]}" run -c opt //oak_benchmarks/linux_cli -- \
        --vm-image="${IMAGE[${platform}]}" --run-vm-script="${RUN_VM_SCRIPT}" \
        --memory-size="${MEMORY}" "${WORKLOAD[@]}" --report-boot-latency \
        --probe-timeout-ms="${PROBE_TIMEOUT_MS}" \
        --poll-interval-ms="${POLL_INTERVAL_MS}" \
        2>>"${log}" | grep '^boot-latency ') || true
      ;;
    *)
      echo "unknown platform: ${platform}" >&2
      exit 1
      ;;
  esac

  if [[ -z ${line} ]]; then
    echo "${platform} iteration ${i}: no boot-latency line; see ${log}" >&2
    exit 1
  fi

  echo "${platform},${i},$(field "${line}" ready_ns),$(field "${line}" launch_ns),$(field "${line}" probe_ns),$(field "${line}" attempts)" >>"${CSV}"
  echo "${platform} ${i}: $(field "${line}" ready_ns) ns" >&2
}

prebuild
write_manifest

echo "platform,iteration,ready_ns,launch_ns,probe_ns,attempts" >"${CSV}"
for p in ${PLATFORMS}; do
  : >"${OUT_DIR}/${p}.log"
done

# Round-robin rather than all of one platform and then all of the next, so that
# a drift in host load over the run is spread across the platforms instead of
# being confounded with them.
for ((i = 0; i < ITERATIONS; i++)); do
  for p in ${PLATFORMS}; do
    take_sample "${p}" "${i}"
  done
done
echo "wrote ${CSV}"

python3 "${REPO_ROOT}/oak_benchmarks/scripts/boot_latency.py" --csv="${CSV}"
