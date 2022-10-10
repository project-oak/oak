#!/bin/bash
# Copyright 2021 The TensorFlow Authors. All Rights Reserved.
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
# ==============================================================================

# Utility script that handles downloading, extracting, and patching third-party
# library dependencies for TensorFlow Lite for Microcontrollers.
# Called with four arguments:
# 1 - URL to download from.
# 2 - MD5 checksum to verify the package's integrity. Use md5sum to create one.
# 3 - Path to new folder to unpack the library into.
# 4 - Optional patching action name.

set -e

# Patches the Ambiq Micro SDK to work around build issues.
patch_am_sdk() {
  local am_dir="${1}"
  if [ ! -f ${am_dir}/VERSION.txt ]; then
    echo "Could not find ${am_dir}, skipping AmbiqMicro SDK patch";
    return;
  fi

  local src_dir=${am_dir}/boards/apollo3_evb/examples/hello_world/gcc
  local dest_dir=${am_dir}/boards/apollo3_evb/examples/hello_world/gcc_patched

  rm -rf ${dest_dir}
  mkdir ${dest_dir}

  cp "${src_dir}/startup_gcc.c" "${dest_dir}/startup_gcc.c"
  cp "${src_dir}/hello_world.ld" "${dest_dir}/apollo3evb.ld"

  sed -i -e '114s/1024/1024\*20/g' "${dest_dir}/startup_gcc.c"
  #sed -i -e 's/main/_main/g' "${dest_dir}/startup_gcc.c"

  sed -i -e '3s/hello_world.ld/apollo3evb.ld/g' "${dest_dir}/apollo3evb.ld"
  sed -i -e '3s/startup_gnu/startup_gcc/g' "${dest_dir}/apollo3evb.ld"
  sed -i -e $'22s/\*(.text\*)/\*(.text\*)\\\n\\\n\\\t\/\* These are the C++ global constructors.  Stick them all here and\\\n\\\t \* then walk through the array in main() calling them all.\\\n\\\t \*\/\\\n\\\t_init_array_start = .;\\\n\\\tKEEP (\*(SORT(.init_array\*)))\\\n\\\t_init_array_end = .;\\\n\\\n\\\t\/\* XXX Currently not doing anything for global destructors. \*\/\\\n/g' "${dest_dir}/apollo3evb.ld"
  sed -i -e $'70s/} > SRAM/} > SRAM\\\n    \/\* Add this to satisfy reference to symbol "end" from libnosys.a(sbrk.o)\\\n     \* to denote the HEAP start.\\\n     \*\/\\\n   end = .;/g' "${dest_dir}/apollo3evb.ld"

  # Add a delay after establishing serial connection
  sed -ir -E $'s/    with serial\.Serial\(args\.port, args\.baud, timeout=12\) as ser:/    with serial.Serial(args.port, args.baud, timeout=12) as ser:\\\n        # Patched.\\\n        import time\\\n        time.sleep(0.25)\\\n        # End patch./g' "${am_dir}/tools/apollo3_scripts/uart_wired_update.py"

  # Add CPP include guards to "am_hal_iom.h"
  sed -i -e '57a\
  #ifdef __cplusplus // Patch\
  extern "C" {\
  #endif // End patch
  ' "${am_dir}/mcu/apollo3/hal/am_hal_iom.h"

  sed -i -e '836a\
  #ifdef __cplusplus // Patch\
  }\
  #endif // End patch
  ' "${am_dir}/mcu/apollo3/hal/am_hal_iom.h"

  echo "Finished preparing Apollo3 files"
}

build_embarc_mli() {
  if [[ ${ARC_TAGS} =~ "mli20_experimental" ]]; then
    make -C ${1}/lib/make build TCF_FILE=${2} BUILDLIB_DIR=${BUILD_LIB_DIR} GEN_EXAMPLES=0 JOBS=4
  else
    make -j 4 -C ${1}/lib/make TCF_FILE=${2}
  fi
}

setup_zephyr() {
  command -v virtualenv >/dev/null 2>&1 || {
    echo >&2 "The required 'virtualenv' tool isn't installed. Try 'pip install virtualenv'."; exit 1;
  }
  virtualenv -p python3 ${1}/venv-zephyr
  . ${1}/venv-zephyr/bin/activate
  python ${1}/venv-zephyr/bin/pip install -r ${1}/scripts/requirements.txt
  west init -m https://github.com/zephyrproject-rtos/zephyr.git
  deactivate
}

# Main function handling the download, verify, extract, and patch process.
download_and_extract() {
  local usage="Usage: download_and_extract URL MD5 DIR [ACTION] [ACTION_PARAM]"
  local url="${1:?${usage}}"
  local expected_md5="${2:?${usage}}"
  local dir="${3:?${usage}}"
  local action=${4}
  local action_param1=${5}  # optional action parameter
  local tempdir=$(mktemp -d)
  local tempdir2=$(mktemp -d)
  local tempfile=${tempdir}/temp_file
  local curl_retries=5

  # Destionation already downloaded.
  if [ -d ${dir} ]; then
      exit 0
  fi

  command -v curl >/dev/null 2>&1 || {
    echo >&2 "The required 'curl' tool isn't installed. Try 'apt-get install curl'."; exit 1;
  }

  echo "downloading ${url}" >&2
  mkdir -p "${dir}"
  # We've been seeing occasional 56 errors from valid URLs, so set up a retry
  # loop to attempt to recover from them.
  for (( i=1; i<=$curl_retries; ++i )); do
    # We have to use this approach because we normally halt the script when
    # there's an error, and instead we want to catch errors so we can retry.
    set +ex
    curl -LsS --fail --retry 5 "${url}" > ${tempfile}
    CURL_RESULT=$?
    set -ex

    # Was the command successful? If so, continue.
    if [[ $CURL_RESULT -eq 0 ]]; then
      break
    fi

    # Keep trying if we see the '56' error code.
    if [[ ( $CURL_RESULT -ne 56 ) || ( $i -eq $curl_retries ) ]]; then
      echo "Error $CURL_RESULT downloading '${url}'"
      exit 1
    fi
    sleep 2
  done

  # Check that the file was downloaded correctly using a checksum.
  DOWNLOADED_MD5=$(openssl dgst -md5 ${tempfile} | sed 's/.* //g')
  if [ ${expected_md5} != ${DOWNLOADED_MD5} ]; then
    echo "Checksum error for '${url}'. Expected ${expected_md5} but found ${DOWNLOADED_MD5}"
    exit 1
  fi

  # delete anything after the '?' in a url that may mask true file extension
  url=$(echo "${url}" | sed "s/\?.*//")

  if [[ "${url}" == *gz ]]; then
    tar -C "${dir}" --strip-components=1 -xzf ${tempfile}
  elif [[ "${url}" == *tar.xz ]]; then
    tar -C "${dir}" --strip-components=1 -xf ${tempfile}
  elif [[ "${url}" == *bz2 ]]; then
    curl -Ls "${url}" > ${tempdir}/tarred.bz2
    tar -C "${dir}" --strip-components=1 -xjf ${tempfile}
  elif [[ "${url}" == *zip ]]; then
    unzip ${tempfile} -d ${tempdir2} 2>&1 1>/dev/null
    # If the zip file contains nested directories, extract the files from the
    # inner directory.
    if [ $(find $tempdir2/* -maxdepth 0 | wc -l) = 1 ] && [ -d $tempdir2/* ]; then
      # unzip has no strip components, so unzip to a temp dir, and move the
      # files we want from the tempdir to destination.
      cp -R ${tempdir2}/*/* ${dir}/
    else
      cp -R ${tempdir2}/* ${dir}/
    fi
  else
    echo "Error unsupported archive type. Failed to extract tool after download."
    exit 1
  fi
  rm -rf ${tempdir2} ${tempdir}

  # Delete any potential BUILD files, which would interfere with Bazel builds.
  find "${dir}" -type f -name '*BUILD' -delete

  if [[ ${action} == "patch_am_sdk" ]]; then
    patch_am_sdk ${dir}
  elif [[ ${action} == "patch_cifar10_dataset" ]]; then
    patch_cifar10_dataset ${dir}
  elif [[ ${action} == "build_embarc_mli" ]]; then
    if [[ "${action_param1}" == *.tcf ]]; then
      cp ${action_param1} ${dir}/hw/arc.tcf
      build_embarc_mli ${dir} ../../hw/arc.tcf
    else
      build_embarc_mli ${dir} ${action_param1}
    fi
  elif [[ ${action} == "setup_zephyr" ]]; then
    setup_zephyr ${dir}
  elif [[ ${action} ]]; then
    echo "Unknown action '${action}'"
    exit 1
  fi
}

download_and_extract "$1" "$2" "$3" "$4" "$5"
