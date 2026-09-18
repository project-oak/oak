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

"""AgentDojo prompt-injection resistance benchmark (`travel` suite).

Reuses the upstream `agentdojo` package (`get_suite`, `load_attack`,
`AgentPipeline`, `OpenAILLM`, and `run_task_with_injection_tasks`) against
Ollama's local OpenAI-compatible endpoint (`/v1`).
"""

import functools
import json
import pathlib
import tempfile
from typing import Any

from agentdojo.agent_pipeline import AgentPipeline, OpenAILLM, PipelineConfig
from agentdojo.attacks import load_attack
from agentdojo.benchmark import run_task_with_injection_tasks
from agentdojo.logging import OutputLogger
from agentdojo.task_suite import get_suite
import openai

from benchmarks.benchmark import Benchmark
from harness.model import Model


class AgentDojo(Benchmark):
  """Evaluates prompt-injection resistance on the AgentDojo `travel` suite."""

  version = "v1.2.2"
  suite = "travel"
  attack = "direct"
  user_tasks = ("user_task_0", "user_task_1")
  injection_tasks = ("injection_task_0", "injection_task_1")

  def run(self, model: Model, out_dir: pathlib.Path) -> pathlib.Path:
    suite = get_suite(self.version, self.suite)

    client = openai.OpenAI(base_url=f"{model.url}/v1", api_key="ollama")
    client.chat.completions.create = functools.partial(
        client.chat.completions.create, seed=model.sampling.seed
    )

    llm = OpenAILLM(
        client=client,
        model=model.name,
        temperature=model.sampling.temperature,
    )
    # AgentPipeline.from_config and attack loaders require a non-None pipeline name.
    llm.name = f"local-{model.name}"

    pipeline = AgentPipeline.from_config(
        PipelineConfig(
            llm=llm,
            model_id=model.name,
            defense=None,
            system_message_name="default",
            system_message=None,
        )
    )
    attack = load_attack(self.attack, suite, pipeline)

    report = out_dir / "report.jsonl"
    with (
        tempfile.TemporaryDirectory() as traces_dir,
        OutputLogger(traces_dir),
        report.open("w") as f,
    ):
      for uid in self.user_tasks:
        user_task = suite.get_user_task_by_id(uid)
        utility_results, security_results = run_task_with_injection_tasks(
            suite=suite,
            agent_pipeline=pipeline,
            user_task=user_task,
            attack=attack,
            logdir=pathlib.Path(traces_dir),
            force_rerun=True,
            injection_tasks=list(self.injection_tasks),
            benchmark_version=self.version,
        )
        for (task_uid, iid), injection_succeeded in security_results.items():
          # In AgentDojo, `security_results[(uid, iid)]` is True when the
          # attacker's injection goal succeeded, and False when the agent resisted.
          record = {
              "suite": self.suite,
              "attack": self.attack,
              "user_task": task_uid,
              "injection_task": iid,
              "utility": bool(utility_results[(task_uid, iid)]),
              "injection_succeeded": bool(injection_succeeded),
              "resisted": not bool(injection_succeeded),
          }
          f.write(json.dumps(record) + "\n")
    return report

  def score(self, report: pathlib.Path) -> dict[str, Any]:
    trials = [json.loads(line) for line in report.read_text().splitlines()]
    if not trials:
      raise ValueError(f"no trials recorded in {report}")

    total = len(trials)
    resisted = sum(t["resisted"] for t in trials)
    utility_passed = sum(t["utility"] for t in trials)
    return {
        "score": resisted / total,
        "detail": {
            "suite": trials[0]["suite"],
            "attack": trials[0]["attack"],
            "trials": total,
            "resisted": resisted,
            "attack_success_rate": (total - resisted) / total,
            "utility_rate": utility_passed / total,
        },
    }
