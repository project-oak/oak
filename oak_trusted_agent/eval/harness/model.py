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

"""The model under evaluation, served by Ollama inside the same container."""

import dataclasses
import os
import time
from typing import Any

import ollama

# Loopback only: nothing outside the container can reach Ollama.
DEFAULT_URL = "http://127.0.0.1:11434"


@dataclasses.dataclass(frozen=True)
class Sampling:
  """Settings that decide whether a rerun reproduces the same score."""

  temperature: float = 0.0
  seed: int = 0


class Model:
  """An Ollama model, and enough about it to make a score meaningful."""

  def __init__(
      self,
      name: str,
      url: str = DEFAULT_URL,
      sampling: Sampling = Sampling(),
      timeout: float = 600.0,
  ):
    self.name = name
    self.url = url
    self.sampling = sampling
    self._client = ollama.Client(host=url, timeout=timeout)

  @classmethod
  def from_env(cls, name: str, sampling: Sampling) -> "Model":
    """Builds a model from `OLLAMA_URL`, which the container sets."""
    return cls(
        name, url=os.getenv("OLLAMA_URL", DEFAULT_URL), sampling=sampling
    )

  def wait_until_ready(self, timeout: float = 120.0) -> None:
    """Blocks until Ollama answers, since it starts alongside us."""
    deadline = time.monotonic() + timeout
    while True:
      try:
        self._client.list()
        return
      except (ConnectionError, ollama.ResponseError) as e:
        if time.monotonic() >= deadline:
          raise RuntimeError(
              f"Ollama did not become ready within {timeout}s"
          ) from e
        time.sleep(1.0)

  def chat(self, prompt: str, system: str | None = None, **options) -> str:
    """Sends one prompt and returns the reply text."""
    messages = [{"role": "user", "content": prompt}]
    if system is not None:
      messages.insert(0, {"role": "system", "content": system})
    response = self._client.chat(
        model=self.name,
        messages=messages,
        options={**dataclasses.asdict(self.sampling), **options},
        keep_alive=-1,  # Keep the weights resident between prompts.
    )
    return response.message.content or ""

  def identity(self) -> dict[str, Any]:
    """Describes what answered, for the `model` field of the predicate."""
    models = self._client.list().models
    entry = next((m for m in models if m.model == self.name), None)
    if entry is None:
      available = ", ".join(sorted(m.model for m in models)) or "none"
      raise RuntimeError(f"{self.name} is not present; available: {available}")

    details = entry.details
    return {
        "name": self.name,
        "digest": _typed(entry.digest),
        "parameters": details.parameter_size if details else None,
        "quantization": details.quantization_level if details else None,
        "sampling": dataclasses.asdict(self.sampling),
    }


def _typed(digest: str) -> str:
  """Spells a digest `algorithm:hex`, as the signer expects."""
  return digest if ":" in digest else f"sha256:{digest}"
