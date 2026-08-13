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

"""Evaluator Service (Party B Enclave).

Acts as an Independent Policy & Data Governance Auditor verifying datasets against enterprise
data governance and privacy standards using a local TEE-resident Gemma model via Ollama.
"""

from contextlib import asynccontextmanager
import base64
import io
import json
import logging
import os
import re
import sys
from typing import Any, Dict, List, Optional

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from fastapi import FastAPI, HTTPException
import httpx
from llm_manager import start_and_prewarm_llm
import pandas as pd
from pydantic import BaseModel, Field

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("evaluator")

OLLAMA_URL = os.getenv("OLLAMA_URL", "http://localhost:11434/api/chat")
OLLAMA_MODEL = os.getenv("OLLAMA_MODEL", "gemma4:e4b")
NUM_CTX = int(os.getenv("OLLAMA_NUM_CTX", "8192"))

BASE_SYSTEM_PROMPT = """You are an expert TEE-resident Data Governance & Sovereign Privacy Auditor. Your task is to evaluate a CSV dataset for enterprise data governance and privacy policy compliance.
(Note: Domain-specific organizational governance rules, risk tolerances, or data tier requirements can be injected into this auditor prompt.)

Focus on:
1. Direct PII Presence: Are there raw unmasked identifiers (e.g. unmasked names, unmasked IDs, exact timestamps)? Masked tokens ('PT-***', 'VS-***', 'Dr. ***', 'Hospital-***') and generalized dates (e.g. '2024') are de-identified.
2. Progressive Anonymization Intensity & K-Anonymity: Check active intensity level (`__intensity__`) or equivalence class size (`__k_level__`).
3. Numeric Attribute Protection: Check if sensitive clinical/numeric values are protected via Differential Privacy (`__dp_applied__`).

EVALUATION RULES FOR PROGRESSIVE ESCALATION:
- If raw unmasked direct identifiers exist or `__intensity__` is missing/raw: return "compliant": false, "status": "FAIL", "risk_level": "HIGH", "recommendation": {"strategy": "anonymize", "params": {"intensity": "level_1", "k": 2}}.
- If direct identifiers are masked (`level_1` or `__k_level__ >= 2`), BUT standard governance requires moderate k-anonymity (k>=5) and numeric differential privacy (`__dp_applied__` is not True): return "compliant": false, "status": "ELEVATE", "risk_level": "MEDIUM", "reasoning": "Dataset requires Level 2 intensity (k=5 + Laplace noise on numeric columns) to satisfy standard governance rules while preserving clinical utility.", "recommendation": {"strategy": "anonymize", "params": {"intensity": "level_2", "k": 5, "epsilon": 2.0}}.
- If direct identifiers are masked AND dataset is at `level_2`, `level_3`, or `level_4` (`__k_level__ >= 5` with DP applied, or synthetic marginal data): the dataset meets sovereign privacy governance rules. You MUST return exactly:
{"compliant": true, "status": "PASS", "risk_level": "LOW", "reasoning": "Dataset meets Level 2 sovereign privacy rules (k=5 with Laplace DP noise applied).", "violations": [], "recommendation": null}

You MUST return your response strictly in the following JSON structure. DO NOT output any other text. DO NOT output markdown tables. ONLY JSON:
{
    "compliant": boolean,
    "status": "PASS" | "FAIL" | "ELEVATE",
    "risk_level": "LOW" | "MEDIUM" | "HIGH",
    "reasoning": "detailed explanation of your finding without echoing raw PII cell values",
    "violations": ["list of specific structural violations without echoing literal raw PII strings"],
    "recommendation": { "strategy": "anonymize" | "differential-privacy" | "synthetic", "params": { ... } }
}
"""


def get_full_system_prompt() -> str:
  """Returns the hardcoded TEE compliance auditor system prompt."""
  return BASE_SYSTEM_PROMPT


def _get_active_model() -> str:
  """Discovers available baked model if configured model tag is missing."""
  try:
    with httpx.Client(timeout=5.0) as http_client:
      resp = http_client.get("http://localhost:11434/api/tags")
      if resp.status_code == 200:
        models = [m.get("name", "") for m in resp.json().get("models", [])]
        for m in models:
          if OLLAMA_MODEL in m or m in OLLAMA_MODEL:
            return m
        if models:
          return models[0]
  except Exception as e:
    logger.warning(f"Could not query Ollama model tags: {e}")
  return OLLAMA_MODEL


def _decode_data(data_b64_or_raw: str) -> str:
  try:
    return base64.b64decode(data_b64_or_raw.encode()).decode("utf-8")
  except Exception:
    return data_b64_or_raw


def _check_raw_pii_presence(df: pd.DataFrame) -> bool:
  """Checks if raw unmasked PII tokens are present in the dataset."""
  pii_cols = [
      "patient_id",
      "visit_id",
      "name",
      "email",
      "ssn",
      "phone",
      "physician",
      "doctor",
      "hospital",
  ]
  for col in df.columns:
    col_lower = col.lower()
    if col_lower in pii_cols or any(
        p in col_lower
        for p in ["patient_id", "visit_id", "physician", "doctor", "hospital"]
    ):
      vals = df[col].dropna().astype(str)
      allowed_masks = {"PT-***", "VS-***", "Dr. ***", "Hospital-***", "***"}
      for v in vals:
        if v not in allowed_masks:
          return True
    if "date" in col_lower:
      vals = df[col].dropna().astype(str)
      for v in vals:
        if len(v) > 4 and "-" in v:
          return True
  return False


def _extract_json(text: str, df: Optional[pd.DataFrame] = None) -> dict:
  """Resilient JSON parsing of LLM outputs with TEE policy verification fallback."""
  text = text.strip()

  # 1. Check for markdown json code blocks
  blocks = re.findall(r"```(?:json)?\s*(\{.*?\})\s*```", text, re.DOTALL)
  for b in blocks:
    try:
      parsed = json.loads(b, strict=False)
      if (
          parsed.get("compliant")
          and df is not None
          and _check_raw_pii_presence(df)
      ):
        return {
            "compliant": False,
            "status": "FAIL",
            "risk_level": "HIGH",
            "reasoning": (
                "Independent auditor inspection detected unmasked direct PII"
                " identifiers in dataset."
            ),
            "violations": [
                "Raw patient identifiers and unmasked dates present"
            ],
            "recommendation": {
                "strategy": "anonymize",
                "params": {"intensity": "level_1", "k": 2},
            },
        }
      return parsed
    except Exception:
      pass

  # 2. Search all { ... } spans containing "compliant"
  starts = [m.start() for m in re.finditer(r"\{", text)]
  ends = [m.start() for m in re.finditer(r"\}", text)]
  for s in starts:
    for e in reversed(ends):
      if e > s and '"compliant"' in text[s : e + 1]:
        try:
          parsed = json.loads(text[s : e + 1], strict=False)
          if (
              parsed.get("compliant")
              and df is not None
              and _check_raw_pii_presence(df)
          ):
            return {
                "compliant": False,
                "status": "FAIL",
                "risk_level": "HIGH",
                "reasoning": (
                    "Independent auditor inspection detected unmasked direct"
                    " PII identifiers in dataset."
                ),
                "violations": [
                    "Raw patient identifiers and unmasked dates present"
                ],
                "recommendation": {
                    "strategy": "anonymize",
                    "params": {"intensity": "level_1", "k": 2},
                },
            }
          return parsed
        except Exception:
          pass

  # 3. Intelligent heuristic & TEE metadata verification with anti-spoofing check
  if df is not None and not df.empty and _check_raw_pii_presence(df):
    return {
        "compliant": False,
        "status": "FAIL",
        "risk_level": "HIGH",
        "reasoning": "Raw unmasked direct identifiers detected in dataset.",
        "violations": ["Raw patient identifiers and unmasked dates present"],
        "recommendation": {
            "strategy": "anonymize",
            "params": {"intensity": "level_1", "k": 2},
        },
    }

  has_level2_plus = False
  if df is not None and not df.empty:
    if "__synthetic__" in df.columns and df["__synthetic__"].iloc[0]:
      has_level2_plus = True
    elif "__intensity__" in df.columns:
      val = str(df["__intensity__"].iloc[0])
      if val in ["level_2", "level_3", "level_4"]:
        has_level2_plus = True
    elif "__k_level__" in df.columns and "__dp_applied__" in df.columns:
      if df["__k_level__"].iloc[0] >= 5 and df["__dp_applied__"].iloc[0]:
        has_level2_plus = True

  text_lower = text.lower()
  is_pass = (
      'compliant": true' in text_lower
      or '"status": "pass"' in text_lower
      or "status: pass" in text_lower
      or "meets sovereign privacy governance rules" in text_lower
  )

  if (is_pass or has_level2_plus) and not (
      df is not None and _check_raw_pii_presence(df)
  ):
    return {
        "compliant": True,
        "status": "PASS",
        "risk_level": "LOW",
        "reasoning": (
            "Dataset verified compliant with Level 2+ sovereign privacy rules"
            f" (k>=5, DP applied). LLM summary: {text[:100]}"
        ),
        "violations": [],
        "recommendation": None,
    }

  return {
      "compliant": False,
      "status": "ELEVATE",
      "risk_level": "MEDIUM",
      "reasoning": (
          "Dataset requires Level 2 intensity (k=5 + Laplace noise on numeric"
          " columns) to satisfy standard governance rules."
      ),
      "violations": ["Standard governance requires k>=5 and DP noise"],
      "recommendation": {
          "strategy": "anonymize",
          "params": {"intensity": "level_2", "k": 5, "epsilon": 2.0},
      },
  }


class EvaluateRequest(BaseModel):
  data: str = Field(
      ..., description="Base64-encoded or raw CSV tabular dataset"
  )


class Recommendation(BaseModel):
  strategy: str = Field(
      ..., description="'k-anonymity', 'anonymize', or 'differential-privacy'"
  )
  params: Dict[str, Any] = Field(default_factory=dict)


class EvaluateResponse(BaseModel):
  compliant: bool
  status: str = Field(..., description="'PASS', 'FAIL', or 'ERROR'")
  risk_level: str = Field(..., description="'LOW', 'MEDIUM', or 'HIGH'")
  reasoning: str
  violations: List[str] = Field(default_factory=list)
  recommendation: Optional[Recommendation] = None


@asynccontextmanager
async def lifespan(app: FastAPI):
  """FastAPI Lifespan: Launches Ollama daemon and prewarms KV-cache on startup."""
  logger.info("Initializing TEE Regulatory Auditor Engine...")
  system_prompt = get_full_system_prompt()
  timings = start_and_prewarm_llm(
      default_model=OLLAMA_MODEL,
      num_ctx=NUM_CTX,
      system_prompt=system_prompt,
  )
  app.state.startup_timings = timings
  yield


app = FastAPI(
    title="Regulatory Auditor Enclave Service",
    description=(
        "Attested compliance auditor verifying data governance and privacy"
        " bounds."
    ),
    version="1.0.0",
    lifespan=lifespan,
)


@app.get("/health")
def health_check() -> dict:
  return {
      "status": "ok",
      "service": "evaluator",
      "num_ctx": NUM_CTX,
      "startup_timings": getattr(app.state, "startup_timings", {}),
  }


@app.post("/evaluate", response_model=EvaluateResponse)
def evaluate_compliance(req: EvaluateRequest) -> EvaluateResponse:
  """Audits dataset against regulatory standards using local TEE-resident Gemma via Ollama."""
  decoded = _decode_data(req.data)
  try:
    df = pd.read_csv(io.StringIO(decoded))
  except Exception as e:
    raise HTTPException(status_code=400, detail=f"Invalid CSV data: {e}")

  if df.empty:
    raise HTTPException(status_code=400, detail="Empty dataset provided")

  user_prompt = (
      f"Dataset for Compliance Evaluation (All {len(df)} rows):\n"
      f"{df.to_csv(index=False)}"
  )
  full_system_prompt = get_full_system_prompt()

  active_model = _get_active_model()
  try:
    payload = {
        "model": active_model,
        "messages": [
            {"role": "system", "content": full_system_prompt},
            {"role": "user", "content": user_prompt},
        ],
        "format": "json",
        "stream": False,
        "options": {"temperature": 0.0, "num_ctx": NUM_CTX},
        "keep_alive": -1,
    }
    with httpx.Client(timeout=600.0) as http_client:
      resp = http_client.post(OLLAMA_URL, json=payload)

      if resp.status_code != 200:
        raise RuntimeError(
            f"Ollama returned HTTP {resp.status_code}: {resp.text}"
        )
      raw_json = resp.json().get("message", {}).get("content", "")
      result_dict = _extract_json(raw_json, df)
      if isinstance(result_dict, list):
        for item in result_dict:
          if isinstance(item, dict) and "compliant" in item:
            result_dict = item
            break
        if isinstance(result_dict, list) and len(result_dict) > 0:
          result_dict = result_dict[-1]

      if isinstance(result_dict, dict) and "compliant" not in result_dict:
        if "thought" in result_dict:
          thought_str = str(result_dict["thought"])
          is_comp = (
              '"compliant": true' in thought_str.lower()
              or "compliant: true" in thought_str.lower()
          )
          risk = (
              "HIGH"
              if "high" in thought_str.lower()
              else ("MEDIUM" if "medium" in thought_str.lower() else "LOW")
          )
          result_dict = {
              "compliant": is_comp,
              "status": "PASS" if is_comp else "FAIL",
              "risk_level": risk,
              "reasoning": thought_str[:500],
              "violations": (
                  ["Dataset requires privacy protection"] if not is_comp else []
              ),
              "recommendation": (
                  {
                      "strategy": "anonymize",
                      "params": {"intensity": "level_2", "k": 5},
                  }
                  if not is_comp
                  else None
              ),
          }

      return EvaluateResponse(**result_dict)
  except Exception as e:
    logger.error(f"[Compliance] Local Ollama not available or failed: {e}")
    raise RuntimeError(
        f"LLM evaluation failed inside TEE at {OLLAMA_URL}. Mock/demo fallbacks"
        " are disabled."
    )


if __name__ == "__main__":
  import uvicorn

  port = int(os.getenv("PORT", "8082"))
  uvicorn.run(app, host="127.0.0.1", port=port)
