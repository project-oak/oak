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

"""Runs one benchmark against the local model and signs what it produced.

python -m harness.run --benchmark=hello_world --model=gemma4:e2b
"""

import argparse
import datetime
import pathlib
import sys

from benchmarks.benchmark import Benchmark
from harness.model import Model, Sampling
from harness.predicate import Predicate
from harness.signer import Signer
from harness.storage import GcsStorage


def _now() -> datetime.datetime:
  """Whole seconds: sub-second timing is noise over a benchmark run."""
  return datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0)


def main(argv: list[str] | None = None) -> None:
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument(
      "--benchmark", required=True, help="directory under benchmarks/"
  )
  parser.add_argument("--model", default="gemma4:e2b")
  parser.add_argument(
      "--out-dir", type=pathlib.Path, default=pathlib.Path("/out")
  )
  parser.add_argument(
      "--signer", type=pathlib.Path, default=pathlib.Path("/bin/signer")
  )
  parser.add_argument("--temperature", type=float, default=0.0)
  parser.add_argument("--seed", type=int, default=0)
  parser.add_argument(
      "--no-attestation",
      action="store_true",
      help="emit an unsigned statement, for running outside Confidential Space",
  )
  parser.add_argument(
      "--upload-to",
      default=None,
      help=(
          "optional gs://<bucket>[/<prefix>] URI to upload the signed bundle to"
      ),
  )
  args = parser.parse_args(argv)

  benchmark = Benchmark.load(args.benchmark)
  out_dir = args.out_dir / benchmark.name
  out_dir.mkdir(parents=True, exist_ok=True)

  model = Model.from_env(args.model, Sampling(args.temperature, args.seed))
  model.wait_until_ready()
  identity = model.identity()

  started_at = _now()
  report = benchmark.run(model, out_dir)
  result = benchmark.score(report)
  finished_at = _now()

  predicate = Predicate.create(
      benchmark=benchmark,
      model=identity,
      result=result,
      started_at=started_at,
      finished_at=finished_at,
  )
  predicate_path = out_dir / "predicate.json"
  predicate_path.write_text(predicate.model_dump_json(indent=2) + "\n")

  print(f"{benchmark.name}: {predicate.score:.3f}", file=sys.stderr)
  Signer(args.signer, attested=not args.no_attestation).sign(
      report, identity, predicate_path, out_dir / "signed.json"
  )
  if args.upload_to:
    subdir = (
        f"{identity.name}/{benchmark.name}".replace(":", "-").replace("_", "-")
    )
    uri = GcsStorage.from_uri(args.upload_to).upload_dir(out_dir, subdir=subdir)
    print(f"uploaded:  {uri}", file=sys.stderr)


if __name__ == "__main__":
  main()
