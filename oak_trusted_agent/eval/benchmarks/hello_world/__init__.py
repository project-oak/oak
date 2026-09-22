#
# Copyright 2026 The Project Oak Authors
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

"""The smallest benchmark that exercises the whole pipeline.

Measures nothing interesting on purpose: it exists so that the container, the
signer and the verifier can be tested end to end, and it needs no accelerator.
"""

import json
import pathlib
from typing import Any

from benchmarks.benchmark import Benchmark
from harness.model import Model

PROMPT = 'Reply with exactly "hello world" and nothing else.'
TRIALS = 10


class HelloWorld(Benchmark):
  """Prompts the model `TRIALS` times and records every reply."""

  version = "1"

  def run(self, model: Model, out_dir: pathlib.Path) -> pathlib.Path:
    report = out_dir / "report.jsonl"
    with report.open("w") as f:
      for trial in range(TRIALS):
        answer = model.chat(PROMPT)
        record = {
            "trial": trial,
            "prompt": PROMPT,
            "answer": answer,
            "passed": _passed(answer),
        }
        f.write(json.dumps(record) + "\n")
    return report

  def score(self, report: pathlib.Path) -> dict[str, Any]:
    trials = [json.loads(line) for line in report.read_text().splitlines()]
    passed = sum(t["passed"] for t in trials)
    return {
        "score": passed / len(trials),
        "detail": {"trials": len(trials), "passed": passed},
    }


def _passed(answer: str) -> bool:
  """Accepts surrounding punctuation and case, but not extra words."""
  return answer.strip().strip(".!\"'").lower() == "hello world"
