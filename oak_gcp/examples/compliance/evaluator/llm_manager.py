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

"""LLM Subprocess & KV-Cache Warmup Manager for Party B Evaluator Enclave.

Handles autonomous lifecycle management of the co-hosted Ollama Gemma daemon,
weight initialization, and 32k context prefix KV-cache prewarming inside TEE.
"""

import logging
import os
import subprocess
import time
from typing import Any, Dict, Optional
import httpx

logger = logging.getLogger("evaluator.llm_manager")


def _get_ollama_url() -> str:
  host = os.getenv("OLLAMA_HOST", "http://127.0.0.1:11434")
  if not host.startswith("http://") and not host.startswith("https://"):
    host = f"http://{host}"
  return host.rstrip("/")


def _is_ollama_running() -> bool:
  """Checks if Ollama daemon is responsive."""
  url = f"{_get_ollama_url()}/api/tags"
  try:
    with httpx.Client(timeout=2.0) as client:
      resp = client.get(url)
      return resp.status_code == 200
  except Exception as e:
    logger.debug(f"Ollama probe failed at {url}: {e}")
    return False


def _get_active_model(target_model: str) -> str:
  """Finds active baked model tag."""
  url = f"{_get_ollama_url()}/api/tags"
  try:
    with httpx.Client(timeout=5.0) as client:
      resp = client.get(url)
      if resp.status_code == 200:
        models = [m.get("name", "") for m in resp.json().get("models", [])]
        for m in models:
          if target_model in m or m in target_model:
            return m
        if models:
          return models[0]
  except Exception as e:
    logger.warning(f"Could not query tags at {url}: {e}")
  return target_model


def start_and_prewarm_llm(
    default_model: str = "gemma4:e4b",
    num_ctx: int = 8192,
    system_prompt: str = "",
) -> Dict[str, Any]:
  """Starts Ollama daemon, preloads model weights, and prewarms KV-cache prefix.

  Returns:
      Structured dictionary detailing staged startup durations and cache statistics.
  """
  timings: Dict[str, Any] = {}

  overall_start = time.perf_counter()

  # Stage 1: Ollama Subprocess Launch & Health Check
  t0 = time.perf_counter()
  if not _is_ollama_running():
    logger.info(f"Launching co-hosted Ollama daemon with num_ctx={num_ctx}...")
    env = os.environ.copy()
    env["OLLAMA_NUM_PARALLEL"] = "1"
    env["OLLAMA_KV_CACHE_TYPE"] = "q4_0"
    env["OLLAMA_FLASH_ATTENTION"] = "1"
    env["LLAMA_ARG_SWA_FULL"] = "true"
    env["OLLAMA_KEEP_ALIVE"] = "-1"
    env["OLLAMA_NUM_CTX"] = str(num_ctx)
    env["OLLAMA_HOST"] = "127.0.0.1:11434"

    # Launch Ollama serve in background with log output
    log_f = open("/tmp/ollama.log", "a")
    subprocess.Popen(
        ["ollama", "serve"],
        env=env,
        stdout=log_f,
        stderr=log_f,
        start_new_session=True,
    )

    # Poll for health
    healthy = False
    for _ in range(40):
      time.sleep(1)
      if _is_ollama_running():
        healthy = True
        break
    if not healthy:
      log_tail = ""
      try:
        with open("/tmp/ollama.log", "r") as f:
          log_tail = f.read()[-1000:]
      except Exception:
        pass
      raise RuntimeError(
          f"Ollama daemon failed to start within timeout. Log:\n{log_tail}"
      )

  else:
    logger.info("Ollama daemon already active.")

  stage1_duration = time.perf_counter() - t0
  timings["stage1_daemon_start_sec"] = round(stage1_duration, 2)
  logger.info(f"Stage 1 (Daemon Ready): {stage1_duration:.2f}s")

  active_model = _get_active_model(default_model)
  timings["active_model"] = active_model
  timings["num_ctx"] = num_ctx

  # Stage 2: Model Weight Loading into RAM
  t0 = time.perf_counter()
  logger.info(
      f"Stage 2: Preloading weights for model '{active_model}' into memory..."
  )
  try:
    with httpx.Client(timeout=300.0) as client:
      resp = client.post(
          f"{_get_ollama_url()}/api/chat",
          json={
              "model": active_model,
              "messages": [{"role": "user", "content": "ping"}],
              "options": {"temperature": 0.0, "num_ctx": num_ctx},
              "stream": False,
              "keep_alive": -1,
          },
      )
      resp.raise_for_status()
  except Exception as e:
    logger.warning(f"Stage 2 model load warning: {e}")

  stage2_duration = time.perf_counter() - t0
  timings["stage2_model_load_sec"] = round(stage2_duration, 2)
  logger.info(f"Stage 2 (Model Weights Loaded): {stage2_duration:.2f}s")

  # Stage 3: KV-Cache Prewarming with Full System Prompt
  t0 = time.perf_counter()
  warmup_user_prompt = "Auditor Prewarm & Initialization Phase."
  chars_count = len(system_prompt) + len(warmup_user_prompt)
  est_tokens = chars_count // 4

  logger.info(
      f"Stage 3: Prewarming KV-cache for {chars_count} chars"
      f" (~{est_tokens} tokens) up to {num_ctx} context..."
  )

  try:
    with httpx.Client(timeout=600.0) as client:
      resp = client.post(
          f"{_get_ollama_url()}/api/chat",
          json={
              "model": active_model,
              "messages": [
                  {"role": "system", "content": system_prompt},
                  {"role": "user", "content": warmup_user_prompt},
              ],
              "options": {"temperature": 0.0, "num_ctx": num_ctx},
              "stream": False,
              "keep_alive": -1,
          },
      )
      resp.raise_for_status()
  except Exception as e:
    logger.warning(f"Stage 3 KV-cache prewarming warning: {e}")

  stage3_duration = time.perf_counter() - t0
  timings["stage3_kv_prewarm_sec"] = round(stage3_duration, 2)
  timings["prewarmed_chars"] = chars_count
  timings["prewarmed_tokens_est"] = est_tokens
  logger.info(f"Stage 3 (KV-Cache Prewarmed): {stage3_duration:.2f}s")

  total_duration = time.perf_counter() - overall_start
  timings["total_startup_sec"] = round(total_duration, 2)
  logger.info(f"Total Engine Ready: {total_duration:.2f}s")

  return timings
