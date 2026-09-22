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

"""The predicate body, as described by `../predicate_schema.md`."""

import datetime
from typing import Any

import pydantic

from benchmarks.benchmark import Benchmark

# A verifier pins this with `--expected-predicate-type`, so a change that is not
# backwards compatible needs a new URI.
PREDICATE_TYPE = "https://project-oak.dev/attestation/model-eval/v1"


# Shapes that exist only as parts of a `Predicate`. Module level rather than
# nested, because a nested `Benchmark` would shadow the imported one in every
# annotation inside the class body.
class _Benchmark(pydantic.BaseModel):
  """Which test was run, and which revision of it."""

  name: str
  version: str


class _Run(pydantic.BaseModel):
  """Unauthenticated. The token's `iat` is the time to believe."""

  started_at: datetime.datetime
  finished_at: datetime.datetime


class Predicate(pydantic.BaseModel):
  """What we claim about the subjects of the statement."""

  benchmark: _Benchmark
  # Whatever `Model.identity` reported.
  model: dict[str, Any]
  # Normalised so that benchmarks compare: higher is always better.
  score: float = pydantic.Field(ge=0.0, le=1.0)
  # The only part whose shape varies between benchmarks.
  detail: dict[str, Any] = {}
  run: _Run

  @classmethod
  def create(
      cls,
      benchmark: Benchmark,
      model: dict[str, Any],
      result: dict[str, Any],
      started_at: datetime.datetime,
      finished_at: datetime.datetime,
  ) -> "Predicate":
    """Assembles what the harness gathered over one benchmark run."""
    return cls(
        benchmark=_Benchmark(name=benchmark.name, version=benchmark.version),
        model=model,
        score=result["score"],
        detail=result.get("detail", {}),
        run=_Run(started_at=started_at, finished_at=finished_at),
    )
