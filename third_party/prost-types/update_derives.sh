#
# Copyright 2024 The Project Oak Authors
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

THIS_SCRIPT_DIR=$(dirname "$0")
find "${THIS_SCRIPT_DIR}" -name '*.rs' -type f -exec sed -i s/::prost::Message/::prost_derive::Message/g {} \;
find "${THIS_SCRIPT_DIR}" -name '*.rs' -type f -exec sed -i s/::prost::Oneof/::prost_derive::Oneof/g {} \;
find "${THIS_SCRIPT_DIR}" -name '*.rs' -type f -exec sed -i s/::prost::Enumeration/::prost_derive::Enumeration/g {} \;
