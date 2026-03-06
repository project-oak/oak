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

import json
import os
import unittest
import sys

class TestConfig(unittest.TestCase):
    def test_config_json(self):
        config_path = os.environ.get("CONFIG_JSON_PATH")
        self.assertTrue(config_path and os.path.exists(config_path))

        with open(config_path, "r") as f:
            config = json.load(f)

        # Verify args
        self.assertIn("process", config)
        self.assertEqual(config["process"]["args"], ["/usr/local/bin/test_binary", "--arg1", "val1"])

        # Verify env
        self.assertIn("env", config["process"])
        env = config["process"]["env"]
        self.assertIn("MY_ENV=test", env)
        # Verify that defaults are present
        self.assertIn("TERM=xterm", env)
        # Verify that defaults can be overridden
        self.assertIn("HOME=/overridden_home", env)
        self.assertNotIn("HOME=/root", env)

    def test_custom_root_path(self):
        config_path = os.environ.get("CUSTOM_ROOT_CONFIG_PATH")
        self.assertTrue(config_path and os.path.exists(config_path))

        with open(config_path, "r") as f:
            config = json.load(f)

        self.assertEqual(config["root"]["path"], "custom_root")

if __name__ == "__main__":
    # Filter out Bazel-specific arguments like --nocapture that unittest doesn't recognize
    args = [arg for arg in sys.argv if not arg.startswith("--nocapture")]
    unittest.main(argv=args)
