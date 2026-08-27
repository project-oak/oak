#!/usr/bin/env bash
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
# Runs the whole benchmark matrix on all three platforms under a fixed CPU
# affinity mask, and writes one CSV per platform plus a manifest describing
# the environment the numbers were taken in.
#
# Every configuration gets the same logical CPUs so that no platform is
# measured on a different part of the machine than another. The default pair
# is two distinct physical cores whose SMT siblings are left out of the mask,
# because a sibling running anything roughly doubles the cost of the crypto
# benchmarks on this part.

set -euo pipefail

CORES="${CORES:-6,7}"
REPETITIONS="${REPETITIONS:-30}"
ITERATIONS="${ITERATIONS:-10000}"
MEMORY_WORKING_SET="${MEMORY_WORKING_SET:-268435456}"
# Run the confidential-computing legs. Off by default because it needs an
# SEV-SNP host: on anything else QEMU refuses to start and every sample fails.
#
# The two runners spell it differently because each inherits the option from a
# different launcher: the enclave goes through `oak_launcher_utils`, whose
# `--vm-type` also covers sev, sev-es and tdx, while `linux_cli` drives
# `run_vm.sh` and has a plain boolean. Nothing here has been run on SNP
# hardware yet.
SNP="${SNP:-0}"
OUT_DIR="${OUT_DIR:-/tmp/oak_matrix_$(date +%Y%m%d_%H%M%S)}"
PLATFORMS="${PLATFORMS:-native oak vm}"

# The full set, in the order it is measured. Overridable from the environment
# as a space-separated list, so that a run which only varies one flag -- the
# 1 GiB working set, say, which sizes just two of these -- does not have to
# re-measure the other seventeen to produce the one point it is after.
#
# check_matrix.py compares platforms benchmark by benchmark, so a narrowed run
# stays checkable; it simply has fewer rows to check.
BENCHMARKS=(
  sha256 sha512 sha3-256 sha3-512
  aes256gcm-seal aes256gcm-open
  p256-sign p256-verify ed25519-sign ed25519-verify
  memory-insert memory-lookup memory-churn array-update alloc-churn
  pointer-chase page-touch null-syscall syscall-control
)
if [[ -n ${BENCHMARKS_OVERRIDE:-} ]]; then
  read -r -a BENCHMARKS <<<"${BENCHMARKS_OVERRIDE}"
fi

# Iteration counts that differ from ITERATIONS, so that no single row
# dominates the wall time of the matrix and so the memory benchmarks reach a
# footprint worth reporting.
#
# page-touch times a whole pass over the working set per iteration and costs
# roughly 15 ms of that on this host, so ten thousand of them would be minutes
# per repetition. The public-key benchmarks are individually expensive for the
# same reason on a smaller scale.
iterations_for() {
  case "$1" in
    page-touch) echo 200 ;;
    p256-verify) echo 3000 ;;
    p256-sign) echo 5000 ;;
    memory-insert | memory-lookup | memory-churn) echo 1000000 ;;
    *) echo "${ITERATIONS}" ;;
  esac
}

# memory-lookup and memory-churn run against a map built before the clock
# starts, and this flag is what sizes it. The 256 MB default is comfortably
# past this host's 32 MiB L3 slice, so both are memory benchmarks rather than
# cache benchmarks.
#
# The evaluation plan also asks for a working set of at least 1 GiB, which is
# a separate run rather than a new default: it multiplies the setup cost of
# every repetition of both memory benchmarks, and the conclusion the plan
# draws from it does not need the rest of the matrix re-measured alongside.
# Set MEMORY_WORKING_SET=1073741824 for that point.
#
# memory-insert builds its map inside the timed loop, one distinct key per
# iteration, so its footprint follows iterations_for. The service gives it a
# one-entry pre-built map whatever this flag says, so passing a size would
# change nothing.
# Per-runner SNP arguments, empty unless SNP=1. See the note on SNP above for
# why the two spellings differ.
OAK_SNP_ARGS=()
VM_SNP_ARGS=()
if [[ ${SNP} == 1 ]]; then
  OAK_SNP_ARGS=(--vm-type=sev-snp)
  VM_SNP_ARGS=(--enable-snp)
fi

working_set_for() {
  case "$1" in
    memory-lookup | memory-churn) echo "${MEMORY_WORKING_SET}" ;;
    *) echo 0 ;;
  esac
}

usage() {
  cat <<EOF
Usage: $0 [--help]

Environment variables:
  CORES=6,7                  Logical CPUs to pin every run to
  REPETITIONS=30             Repetitions per benchmark, reported as median and IQR
  ITERATIONS=10000           Timed iterations per repetition
  MEMORY_WORKING_SET=256MB   Working set for memory-lookup and memory-churn, in
                             bytes. Use 1073741824 for the plan's >=1 GiB point.
  SNP=0                      Set to 1 to run the SEV-SNP legs. Needs an SNP
                             host; untested, as no such host is available yet.
  BENCHMARKS_OVERRIDE=...    Space-separated benchmark names, to narrow the run
                             to a subset of the matrix.
  PLATFORMS="native oak vm"  Which platforms to measure
  OUT_DIR=<path>             Where to write the CSVs and the manifest

Exits non-zero when check_matrix.py finds the platforms incomparable. The CSVs
are still written; only the claim that they may be compared is withheld.
EOF
}

if [[ "${1:-}" == "--help" || "${1:-}" == "-h" ]]; then
  usage
  exit 0
fi

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${REPO_ROOT}"

mkdir -p "${OUT_DIR}"

BAZEL=(direnv exec "${REPO_ROOT}" bazel)
PIN=(taskset -c "${CORES}")

# Records what the run could and could not control, so a reader can tell
# whether two CSVs are comparable without having to trust that the machine was
# in the same state for both.
write_manifest() {
  local f="${OUT_DIR}/manifest.txt"
  {
    echo "date: $(date -Is)"
    echo "host: $(uname -n), kernel $(uname -r)"
    echo "cpu: $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ //')"
    echo "pinned to logical CPUs: ${CORES}"
    for c in ${CORES//,/ }; do
      echo "  cpu${c} siblings: $(cat "/sys/devices/system/cpu/cpu${c}/topology/thread_siblings_list")"
    done
    echo "smt: $(cat /sys/devices/system/cpu/smt/control 2>/dev/null || echo unknown)"
    echo "governor: $(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
    echo "boost: $(cat /sys/devices/system/cpu/cpufreq/boost 2>/dev/null || echo unknown)"
    echo "thp: $(cat /sys/kernel/mm/transparent_hugepage/enabled 2>/dev/null || echo unknown)"
    echo "ksm: $(cat /sys/kernel/mm/ksm/run 2>/dev/null || echo unknown)"
    echo "cmdline: $(cat /proc/cmdline)"
    echo "repetitions: ${REPETITIONS}"
    echo "iterations: ${ITERATIONS}"
    echo "memory working set: ${MEMORY_WORKING_SET} bytes"
    echo "benchmarks: ${BENCHMARKS[*]}"
    echo "sev-snp: ${SNP}"
    echo "revision: $(jj --ignore-working-copy log -r @ --no-graph -T 'commit_id' 2>/dev/null || echo unknown)"
    echo
    echo "not controlled:"
    echo "  the governor and SMT need root and were left as found"
    echo "  the SMT siblings of the pinned CPUs are excluded from the mask, but"
    echo "  the kernel may still schedule unrelated work onto them"
  } >"${f}"
  echo "wrote ${f}"
}

# Builds first, for two reasons.
#
# The runners below send stdout to the CSV, because that is where the benchmark
# writes its rows. A build triggered by the first `bazel run` puts its own
# output on that same stream: the VM image genrule runs unsandboxed and prints
# a banner, which lands above the CSV header and makes the file unparseable.
# Only the first run of a fresh output base sees this, which is why it stayed
# hidden for so long.
#
# It also keeps compilation out of the measurement. A build inside the first
# invocation would be charged to whichever benchmark happened to run first.
prebuild() {
  echo "building..." >&2
  for p in ${PLATFORMS}; do
    case "${p}" in
      native) "${BAZEL[@]}" build -c opt //oak_benchmarks/linux_enclave_app ;;
      oak) "${BAZEL[@]}" build -c opt //oak_benchmarks/oak_enclave_app:oak_enclave_app_run ;;
      vm)
        "${BAZEL[@]}" build -c opt \
          //oak_benchmarks/linux_cli \
          //oak_benchmarks/linux_enclave_app:linux_enclave_image_run
        ;;
      *)
        echo "unknown platform: ${p}" >&2
        exit 1
        ;;
    esac
  done >&2
}

run_native() {
  local out="${OUT_DIR}/native.csv"
  local log="${OUT_DIR}/native.log"
  : >"${out}"
  : >"${log}"
  local header="--csv-header"
  for b in "${BENCHMARKS[@]}"; do
    local n w
    n="$(iterations_for "${b}")"
    w="$(working_set_for "${b}")"
    echo "native ${b} (${n} iterations)" >&2
    "${PIN[@]}" "${BAZEL[@]}" run -c opt //oak_benchmarks/linux_enclave_app -- \
      --benchmark="${b}" --iterations="${n}" --working-set-size="${w}" \
      --repetitions="${REPETITIONS}" --output=csv ${header} \
      2>>"${log}" >>"${out}"
    header=""
  done
  echo "wrote ${out}"
}

run_oak() {
  local out="${OUT_DIR}/oak.csv"
  local log="${OUT_DIR}/oak.log"
  : >"${out}"
  : >"${log}"
  local header="--csv-header"
  for b in "${BENCHMARKS[@]}"; do
    local n w
    n="$(iterations_for "${b}")"
    w="$(working_set_for "${b}")"
    echo "oak ${b} (${n} iterations)" >&2
    "${PIN[@]}" "${BAZEL[@]}" run -c opt \
      //oak_benchmarks/oak_enclave_app:oak_enclave_app_run -- \
      --memory-size=1024M --benchmark="${b}" --iterations="${n}" --working-set-size="${w}" \
      --repetitions="${REPETITIONS}" --output=csv ${header} "${OAK_SNP_ARGS[@]}" \
      2>>"${log}" >>"${out}"
    header=""
  done
  echo "wrote ${out}"
}

run_vm() {
  local out="${OUT_DIR}/vm.csv"
  local log="${OUT_DIR}/vm.log"
  : >"${out}"
  : >"${log}"
  local header="--csv-header"
  for b in "${BENCHMARKS[@]}"; do
    local n w
    n="$(iterations_for "${b}")"
    w="$(working_set_for "${b}")"
    echo "vm ${b} (${n} iterations)" >&2
    "${PIN[@]}" "${BAZEL[@]}" run -c opt \
      //oak_benchmarks/linux_enclave_app:linux_enclave_image_run -- \
      --benchmark="${b}" --iterations="${n}" --working-set-size="${w}" \
      --repetitions="${REPETITIONS}" --output=csv ${header} "${VM_SNP_ARGS[@]}" \
      2>>"${log}" >>"${out}"
    header=""
  done
  echo "wrote ${out}"
}

# A reused OUT_DIR would otherwise leave a previous run's CSV in place for any
# platform this run is not measuring, and the checker would compare it against
# today's without noticing.
rm -f "${OUT_DIR}"/*.csv "${OUT_DIR}"/*.log

prebuild
write_manifest
for p in ${PLATFORMS}; do
  case "${p}" in
    native) run_native ;;
    oak) run_oak ;;
    vm) run_vm ;;
    *)
      echo "unknown platform: ${p}" >&2
      exit 1
      ;;
  esac
done

echo "matrix complete: ${OUT_DIR}"

# Nothing above establishes that the CSVs may be placed side by side. The
# checker does, and its exit status becomes this script's, so a matrix whose
# platforms disagree cannot be mistaken for one that succeeded.
python3 "${REPO_ROOT}/oak_benchmarks/scripts/check_matrix.py" \
  --dir="${OUT_DIR}" --platforms="${PLATFORMS}"
