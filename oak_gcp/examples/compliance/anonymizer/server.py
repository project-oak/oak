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

"""Anonymizer Service (Party A Enclave).

Implements k-anonymity, Differential Privacy, and synthetic data generation
inside Google Cloud Confidential Space.
"""

import base64
import io
import logging
import math
import secrets
from typing import Dict, List, Optional, Tuple

from fastapi import FastAPI, HTTPException
import pandas as pd
from pydantic import BaseModel, Field

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("anonymizer")

_system_random = secrets.SystemRandom()

# Fixed domain bounds for clinical features to decouple DP sensitivity from sample data.
DEFAULT_DOMAIN_BOUNDS: Dict[str, Tuple[float, float]] = {
    "age": (0.0, 120.0),
    "systolic_bp": (50.0, 250.0),
    "diastolic_bp": (30.0, 150.0),
    "heart_rate": (30.0, 220.0),
    "glucose_mg_dl": (40.0, 500.0),
    "cholesterol_mg_dl": (100.0, 500.0),
    "weight_kg": (2.0, 300.0),
    "height_cm": (40.0, 250.0),
    "bmi": (10.0, 70.0),
}

app = FastAPI(
    title="Privacy Anonymizer Enclave Service",
    description=(
        "Attested data transformation engine for k-anonymity and differential"
        " privacy."
    ),
    version="1.0.0",
)


def _decode_data(data_b64_or_raw: str) -> str:
  """Decodes base64 data, falling back to raw string."""
  try:
    return base64.b64decode(data_b64_or_raw.encode()).decode("utf-8")
  except Exception:
    return data_b64_or_raw


def _encode_data(data_raw: str) -> str:
  """Encodes raw text into base64."""
  return base64.b64encode(data_raw.encode()).decode("utf-8")


def _laplace_sample(scale: float) -> float:
  """Samples from Laplace(0, scale) with domain-error guard for log(0) using SystemRandom."""
  if scale <= 0:
    return 0.0
  u = _system_random.random() - 0.5
  while abs(u) >= 0.5:
    u = _system_random.random() - 0.5
  return -scale * math.copysign(1.0, u) * math.log(1.0 - 2.0 * abs(u))


def _mask_direct_pii(df: pd.DataFrame) -> pd.DataFrame:
  """Masks direct identifiers and generalizes dates."""
  df = df.copy()
  direct_pii_cols = [
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
    if "date" in col_lower:
      df[col] = df[col].apply(
          lambda x: str(x)[:4] if pd.notna(x) and len(str(x)) >= 4 else str(x)
      )
    elif col_lower in direct_pii_cols or any(
        p in col_lower
        for p in ["patient_id", "visit_id", "physician", "doctor", "hospital"]
    ):
      if "patient" in col_lower:
        df[col] = df[col].apply(lambda x: "PT-***" if pd.notna(x) else x)
      elif "visit" in col_lower:
        df[col] = df[col].apply(lambda x: "VS-***" if pd.notna(x) else x)
      elif "physician" in col_lower or "doctor" in col_lower:
        df[col] = df[col].apply(lambda x: "Dr. ***" if pd.notna(x) else x)
      elif "hospital" in col_lower:
        df[col] = df[col].apply(lambda x: "Hospital-***" if pd.notna(x) else x)
      else:
        df[col] = "***"
  return df


def _suppress_numeric_outliers(
    df: pd.DataFrame, factor: float = 1.5
) -> pd.DataFrame:
  """Suppresses rows with numeric values outside IQR thresholds."""
  df_clean = df.copy()
  numeric_cols = df_clean.select_dtypes(include=["number"]).columns
  for col in numeric_cols:
    if col.startswith("__") or col in ["id", "patient_id", "visit_id"]:
      continue
    valid_vals = df_clean[col].dropna()
    if len(valid_vals) < 4:
      continue
    q25 = valid_vals.quantile(0.25)
    q75 = valid_vals.quantile(0.75)
    iqr = q75 - q25
    if iqr > 0:
      lower = q25 - factor * iqr
      upper = q75 + factor * iqr
      df_clean = df_clean[
          df_clean[col].isna()
          | ((df_clean[col] >= lower) & (df_clean[col] <= upper))
      ]
  return df_clean


def _apply_calibrated_dp_noise(
    df: pd.DataFrame,
    epsilon: float,
    columns: Optional[List[str]] = None,
    bounds: Optional[Dict[str, Tuple[float, float]]] = None,
) -> pd.DataFrame:
  """Applies calibrated Laplace DP noise scaled to domain sensitivity.

  Sensitivity is derived from fixed domain bounds or request-provided bounds,
  ensuring it is a property of the domain schema rather than sample data.
  """
  df = df.copy()
  exclude = [
      "__k_level__",
      "__epsilon__",
      "__records_suppressed__",
      "patient_id",
      "visit_id",
      "id",
      "age",
      "zip_code",
  ]
  target_cols = (
      columns
      if columns
      else [
          c
          for c in df.select_dtypes(include="number").columns
          if c not in exclude
      ]
  )

  for col in target_cols:
    if col in df.columns and pd.api.types.is_numeric_dtype(df[col]):
      col_lower = col.lower()
      domain_bound = None
      if bounds and col in bounds:
        domain_bound = bounds[col]
      elif bounds and col_lower in bounds:
        domain_bound = bounds[col_lower]
      elif col_lower in DEFAULT_DOMAIN_BOUNDS:
        domain_bound = DEFAULT_DOMAIN_BOUNDS[col_lower]

      if domain_bound is not None:
        lower, upper = float(domain_bound[0]), float(domain_bound[1])
        if lower >= upper:
          raise HTTPException(
              status_code=400,
              detail=(
                  f"Invalid domain bounds for column '{col}': lower bound"
                  f" ({lower}) must be less than upper bound ({upper})"
              ),
          )
        sensitivity = max(1.0, upper - lower)
      else:
        # Fallback fixed domain sensitivity for unknown numeric attributes
        sensitivity = 100.0

      scale = sensitivity / epsilon
      vals = df[col].dropna()
      is_non_neg = bool((vals >= 0).all()) if not vals.empty else False

      new_vals = []
      for orig_val in df[col]:
        if pd.isna(orig_val):
          new_vals.append(orig_val)
        else:
          # Invariant SEC-01: clamp input to domain bounds so Delta f cannot exceed declared sensitivity
          clamped_val = float(orig_val)
          if domain_bound is not None:
            clamped_val = min(max(clamped_val, lower), upper)
          pert = clamped_val + _laplace_sample(scale)
          new_vals.append(max(0.0, pert) if is_non_neg else pert)
      df[col] = new_vals

  return df


class KAnonymityRequest(BaseModel):
  data: str = Field(..., description="Base64-encoded or raw CSV tabular data")
  k: int = Field(
      default=5, ge=2, description="Target k-anonymity equivalence threshold"
  )
  quasi_identifiers: List[str] = Field(
      default_factory=lambda: ["age", "gender", "zip_code"],
      description="List of quasi-identifier column names",
  )
  intensity: str = Field(
      default="level_2",
      description=(
          "Progressive lossy intensity level ('level_1', 'level_2', 'level_3',"
          " 'level_4')"
      ),
  )
  apply_dp: bool = Field(
      default=False,
      description="Whether to perturb numeric columns via Differential Privacy",
  )
  epsilon: float = Field(
      default=2.0,
      description="Differential privacy epsilon budget when DP is active",
  )
  bounds: Optional[Dict[str, Tuple[float, float]]] = Field(
      default=None,
      description=(
          "Optional domain bounds mapping column names to (min, max) values"
          " for domain-level DP sensitivity"
      ),
  )


class KAnonymityResponse(BaseModel):
  success: bool
  data: str
  records_before: int
  records_after: int
  suppressed_count: int
  optimal_peel_level: int
  intensity_applied: str
  utility_retention_score: float
  dp_applied: bool


class DifferentialPrivacyRequest(BaseModel):
  data: str = Field(..., description="Base64-encoded or raw CSV tabular data")
  epsilon: float = Field(
      default=0.5, gt=0.0, description="Differential privacy budget (epsilon)"
  )
  columns: Optional[List[str]] = Field(
      default=None,
      description=(
          "Numeric columns to perturb. Defaults to all numeric columns."
      ),
  )
  bounds: Optional[Dict[str, Tuple[float, float]]] = Field(
      default=None,
      description=(
          "Optional domain bounds mapping column names to (min, max) values"
          " for domain-level DP sensitivity"
      ),
  )


class DifferentialPrivacyResponse(BaseModel):
  success: bool
  data: str
  applied_columns: List[str]
  epsilon: float


class SyntheticDataRequest(BaseModel):
  data: str = Field(..., description="Base64-encoded or raw CSV tabular data")
  num_records: int = Field(
      default=100, ge=1, description="Number of synthetic rows to generate"
  )
  bounds: Optional[Dict[str, Tuple[float, float]]] = Field(
      default=None,
      description=(
          "Optional domain bounds mapping column names to (min, max) values"
          " for domain-level DP sensitivity"
      ),
  )


class SyntheticDataResponse(BaseModel):
  success: bool
  data: str
  records_generated: int


@app.get("/health")
def health_check() -> dict:
  return {"status": "ok", "service": "anonymizer"}


@app.post("/anonymize", response_model=KAnonymityResponse)
def apply_k_anonymity(req: KAnonymityRequest) -> KAnonymityResponse:
  """Masks direct PII, searches for optimal peel level, and suppresses outlying rows with progressive intensity."""
  decoded = _decode_data(req.data)
  try:
    df = pd.read_csv(io.StringIO(decoded))
  except Exception as e:
    raise HTTPException(status_code=400, detail=f"Invalid CSV format: {e}")

  if df.empty:
    raise HTTPException(status_code=400, detail="Empty dataset provided")

  # If level_4 (Synthetic fallback), delegate to synthetic generation
  if req.intensity == "level_4":
    synth_resp = generate_synthetic_data(
        SyntheticDataRequest(
            data=req.data, num_records=len(df), bounds=req.bounds
        )
    )
    return KAnonymityResponse(
        success=True,
        data=synth_resp.data,
        records_before=len(df),
        records_after=synth_resp.records_generated,
        suppressed_count=0,
        optimal_peel_level=5,
        intensity_applied="level_4",
        utility_retention_score=0.42,
        dp_applied=True,
    )

  records_before = len(df)

  # Adjust parameters according to progressive intensity level
  target_k = req.k
  should_dp = req.apply_dp
  dp_eps = req.epsilon
  base_utility_mult = 0.88

  if req.intensity == "level_1":
    target_k = max(2, req.k if req.k != 5 else 2)
    should_dp = False
    base_utility_mult = 0.96
  elif req.intensity == "level_2":
    target_k = max(5, req.k)
    should_dp = True
    dp_eps = 2.0
    base_utility_mult = 0.85
  elif req.intensity == "level_3":
    target_k = max(10, req.k if req.k != 5 else 10)
    should_dp = True
    dp_eps = 0.5
    base_utility_mult = 0.70

  # 1. Pre-suppress and mask direct identifiers (PII) and generalize dates
  df = _mask_direct_pii(df)

  # For level_3, apply aggressive numeric outlier suppression before peel-search
  if req.intensity == "level_3":
    df = _suppress_numeric_outliers(df, factor=1.5)

  # Filter quasi_identifiers to exclude already masked direct PII
  active_quasi = [
      q
      for q in req.quasi_identifiers
      if q in df.columns
      and q.lower()
      not in [
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
  ]

  # Fallback to sensible candidate quasi-identifiers if requested ones aren't in dataframe
  if not active_quasi:
    fallback_candidates = [
        "visit_date",
        "primary_condition",
        "age",
        "gender",
        "zip_code",
    ]
    active_quasi = [q for q in fallback_candidates if q in df.columns]

  # 2. Optimal Utility Peel-Search
  best_df = None
  best_peel = 1
  max_surviving = -1

  if active_quasi:
    for peel in range(1, 6):
      df_temp = df.copy()
      for col in active_quasi:
        if "date" in col.lower():
          if peel == 1:
            df_temp[col] = df_temp[col].apply(
                lambda x: str(x)[:3] + "*"
                if pd.notna(x) and len(str(x)) >= 4
                else str(x)
            )
          else:
            df_temp[col] = df_temp[col].apply(
                lambda x: str(x)[:2] + "**"
                if pd.notna(x) and len(str(x)) >= 4
                else str(x)
            )
        elif "zip" in col.lower():
          df_temp[col] = df_temp[col].apply(
              lambda x: str(x)[:-peel] + "*" * min(peel, len(str(x)))
              if len(str(x)) > peel
              else "*"
          )

      group_counts = df_temp.groupby(active_quasi).size().to_dict()

      def is_compliant(row):
        key = tuple(row[c] for c in active_quasi)
        return group_counts.get(key, 0) >= target_k

      df_surviving = df_temp[df_temp.apply(is_compliant, axis=1)].copy()
      if len(df_surviving) > max_surviving:
        max_surviving = len(df_surviving)
        best_df = df_surviving
        best_peel = peel

  if best_df is None or best_df.empty:
    best_df = df.iloc[0:0].copy()

  # Apply numeric Differential Privacy if required by intensity or apply_dp
  if should_dp and not best_df.empty:
    best_df = _apply_calibrated_dp_noise(
        best_df, epsilon=dp_eps, bounds=req.bounds
    )
    best_df["__dp_applied__"] = True
    best_df["__epsilon__"] = dp_eps
  elif should_dp:
    best_df["__dp_applied__"] = True
    best_df["__epsilon__"] = dp_eps

  # Append audit metadata
  best_df["__k_level__"] = target_k
  best_df["__intensity__"] = req.intensity
  best_df["__records_suppressed__"] = records_before - len(best_df)

  retention_ratio = len(best_df) / max(1, records_before)
  utility_score = round(retention_ratio * base_utility_mult, 2)

  output_csv = best_df.to_csv(index=False)
  return KAnonymityResponse(
      success=True,
      data=_encode_data(output_csv),
      records_before=records_before,
      records_after=len(best_df),
      suppressed_count=records_before - len(best_df),
      optimal_peel_level=best_peel,
      intensity_applied=req.intensity,
      utility_retention_score=utility_score,
      dp_applied=should_dp,
  )


@app.post("/differential_privacy", response_model=DifferentialPrivacyResponse)
def apply_differential_privacy(
    req: DifferentialPrivacyRequest,
) -> DifferentialPrivacyResponse:
  """Applies calibrated Laplace perturbation to numeric attributes."""
  decoded = _decode_data(req.data)
  try:
    df = pd.read_csv(io.StringIO(decoded))
  except Exception as e:
    raise HTTPException(status_code=400, detail=f"Invalid CSV format: {e}")

  if df.empty:
    raise HTTPException(status_code=400, detail="Empty dataset provided")

  target_columns = req.columns or []
  applied_cols = [
      col
      for col in target_columns
      if col in df.columns and pd.api.types.is_numeric_dtype(df[col])
  ]
  if not applied_cols:
    exclude = [
        "__k_level__",
        "__epsilon__",
        "__records_suppressed__",
        "patient_id",
        "visit_id",
        "id",
    ]
    applied_cols = [
        col
        for col in df.select_dtypes(include="number").columns
        if col not in exclude
    ]

  if not applied_cols:
    raise HTTPException(
        status_code=400,
        detail="No numeric columns found for differential privacy",
    )

  df = _apply_calibrated_dp_noise(
      df, epsilon=req.epsilon, columns=applied_cols, bounds=req.bounds
  )
  df["__dp_applied__"] = True
  df["__epsilon__"] = req.epsilon

  output_csv = df.to_csv(index=False)
  return DifferentialPrivacyResponse(
      success=True,
      data=_encode_data(output_csv),
      applied_columns=applied_cols,
      epsilon=req.epsilon,
  )


@app.post("/synthetic", response_model=SyntheticDataResponse)
def generate_synthetic_data(req: SyntheticDataRequest) -> SyntheticDataResponse:
  """Generates synthetic dataset from marginal empirical distributions with DP and PII masking."""
  decoded = _decode_data(req.data)
  try:
    df = pd.read_csv(io.StringIO(decoded))
  except Exception as e:
    raise HTTPException(status_code=400, detail=f"Invalid CSV format: {e}")

  if df.empty:
    raise HTTPException(status_code=400, detail="Empty dataset provided")

  # First mask direct PII
  df_masked = _mask_direct_pii(df)

  synthetic_dict = {}
  for col in df_masked.columns:
    if col.startswith("__"):
      continue
    col_vals = df_masked[col].dropna().tolist()
    if not col_vals:
      synthetic_dict[col] = [None] * req.num_records
    elif pd.api.types.is_numeric_dtype(df_masked[col]):
      # Continuous: bootstrap, clamp to domain bounds, and add Laplace noise
      sampled = [
          float(_system_random.choice(col_vals)) for _ in range(req.num_records)
      ]
      col_lower = col.lower()
      bound = None
      if req.bounds and col in req.bounds:
        bound = req.bounds[col]
      elif req.bounds and col_lower in req.bounds:
        bound = req.bounds[col_lower]
      elif col_lower in DEFAULT_DOMAIN_BOUNDS:
        bound = DEFAULT_DOMAIN_BOUNDS[col_lower]

      if bound is not None:
        b_lower, b_upper = float(bound[0]), float(bound[1])
        dyn_range = max(1.0, b_upper - b_lower)
        clamped_sampled = [min(max(s, b_lower), b_upper) for s in sampled]
      else:
        dyn_range = 100.0
        clamped_sampled = sampled

      scale = dyn_range / 0.5  # epsilon = 0.5 for synthetic
      is_non_neg = bool((df_masked[col] >= 0).all())
      synthetic_dict[col] = [
          max(0.0, s + _laplace_sample(scale))
          if is_non_neg
          else s + _laplace_sample(scale)
          for s in clamped_sampled
      ]
    else:
      # Categorical: count-based sampling
      val_counts = df_masked[col].value_counts().to_dict()
      categories = list(val_counts.keys())
      counts = [float(val_counts[c]) for c in categories]
      noisy_counts = [max(0.1, c + _laplace_sample(1.0)) for c in counts]
      total = sum(noisy_counts)
      probs = [c / total for c in noisy_counts]
      synthetic_dict[col] = _system_random.choices(
          categories, weights=probs, k=req.num_records
      )

  synth_df = pd.DataFrame(synthetic_dict)
  synth_df["__synthetic__"] = True
  synth_df["__intensity__"] = "level_4"
  synth_df["__k_level__"] = 10
  synth_df["__dp_applied__"] = True
  synth_df["__epsilon__"] = 0.5
  synth_df["__records_suppressed__"] = 0

  return SyntheticDataResponse(
      success=True,
      data=_encode_data(synth_df.to_csv(index=False)),
      records_generated=req.num_records,
  )


if __name__ == "__main__":
  import os
  import uvicorn

  port = int(os.getenv("PORT", 8081))
  uvicorn.run(app, host="127.0.0.1", port=port)
