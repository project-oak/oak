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

"""Base class implemented by every benchmark under `benchmarks/`."""

import abc
import importlib
import pathlib
from typing import Any

from harness.model import Model


class Benchmark(abc.ABC):
  """Common interface implemented by every benchmark under `benchmarks/`."""

  name: str
  version: str

  @abc.abstractmethod
  def run(self, model: Model, out_dir: pathlib.Path) -> pathlib.Path:
    """Runs the benchmark and returns the path to the report it wrote."""

  @abc.abstractmethod
  def score(self, report: pathlib.Path) -> dict[str, Any]:
    """Reduces a report to `{"score": float, "detail": {...}}`."""

  @classmethod
  def load(cls, name: str) -> "Benchmark":
    """Loads and instantiates the Benchmark subclass in `benchmarks.<name>`."""
    try:
      module = importlib.import_module(f"benchmarks.{name}")
    except ImportError as e:
      raise SystemExit(f"no benchmark named {name}: {e}") from e

    for obj in vars(module).values():
      if isinstance(obj, type) and issubclass(obj, cls) and obj is not cls:
        instance = obj()
        instance.name = name
        return instance
    raise SystemExit(f"benchmarks/{name} does not define a Benchmark subclass")
