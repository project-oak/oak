#
# Copyright 2025 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the 'License');
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an 'AS IS' BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

import argparse
import json


def create_lookup_data_entry(key, value_json):
    """Creates a textproto entry for LookupDataChunk."""
    # We need to escape backslashes and quotes.
    escaped_value = value_json.replace("\\", "\\\\").replace('"', '\\"')
    return f"""items: {{
  key: "{key}"
  value: "{escaped_value}"
}}
"""


def main():
    parser = argparse.ArgumentParser(
        description="Create lookup data textproto from JSON files."
    )
    parser.add_argument(
        "--input_json",
        nargs="+",
        required=True,
        help="Input JSON files",
    )
    parser.add_argument(
        "--output_textproto",
        required=True,
        help="Output textproto lookup data file",
    )
    args = parser.parse_args()

    lookup_data_map = {}

    for input_file in args.input_json:
        with open(input_file, "r") as f:
            data = json.load(f)
            # Assuming the JSON contains a single top-level key which is a list of
            # objects.
            if len(data) != 1:
                raise ValueError(
                    f"Expected 1 top-level key in {input_file}, found {len(data)}"
                )

            top_level_key = list(data.keys())[0]
            entries = data[top_level_key]

            for entry in entries:
                # Assuming each entry has a single key (e.g., "flight")
                if len(entry) != 1:
                    raise ValueError(
                        f"Expected 1 inner key in entry {entry}, found {len(entry)}"
                    )

                inner_key = list(entry.keys())[0]
                item_data = entry[inner_key]

                if "key" not in item_data:
                    raise ValueError(f"Missing 'key' in item {item_data}")

                key = item_data["key"]
                value_data = item_data.copy()
                del value_data["key"]

                if key not in lookup_data_map:
                    lookup_data_map[key] = []
                lookup_data_map[key].append(value_data)

    with open(args.output_textproto, "w") as output_file:
        output_file.write(
            "# proto-file: proto/oak_functions/service/oak_functions.proto\n"
        )
        output_file.write("# proto-message: oak.functions.LookupDataChunk\n\n")

        for key, value_list in lookup_data_map.items():
            # Use compact representation.
            value_json = json.dumps(value_list, separators=(",", ":"))
            output_file.write(create_lookup_data_entry(key, value_json))


if __name__ == "__main__":
    main()
