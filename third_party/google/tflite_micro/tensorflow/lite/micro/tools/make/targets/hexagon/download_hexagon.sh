#!/bin/bash

# Copyright 2020 The TensorFlow Authors. All Rights Reserved.
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

# TODO(b/190754463): Delete this script once we have the Hexagon kernels checked
# in and integrated for all the workflows.
#
# Explanation and background can be found in:
# https://docs.google.com/document/d/1SlU5OcHEjdgs02ZCupo21mlLBJ6tE6D46FxUrQl8xUc/edit#heading=h.fshpxalu2qt4

# Usage: ./tensorflow/lite/micro/tools/make/targets/hexagon/download_hexagon.sh <path-to-hexagon_tflm_core.a>

# Clone hexagon kernels to temp directory and check out known-good commit.
HEXAGON_DIR=/tmp/hexagon_optimized

if [ ! -d ${HEXAGON_DIR} ]; then
  mkdir -p ${HEXAGON_DIR}
  git clone -b release_v2 https://source.codeaurora.org/quic/embedded_ai/tensorflow ${HEXAGON_DIR}
fi

pushd ${HEXAGON_DIR} > /dev/null
git checkout 2d052806c211144875c89315a4fc6f1393064cf6
popd > /dev/null

# Copy optimized kernels from checkout, copy prebuilt lib.
rm -rf tensorflow/lite/micro/kernels/hexagon
cp -R ${HEXAGON_DIR}/tensorflow/lite/micro/kernels/hexagon tensorflow/lite/micro/kernels/hexagon
mkdir tensorflow/lite/micro/kernels/hexagon/lib
cp ${1} tensorflow/lite/micro/kernels/hexagon/lib/
