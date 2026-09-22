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

"""The signer binary, which turns artifacts into a signed in-toto statement."""

import pathlib
import subprocess
from typing import Any

from harness.predicate import PREDICATE_TYPE


class Signer:
  """The signer, which has to live in this same container image.

  The Confidential Space launcher stamps the requesting image into the token,
  so a signer running anywhere else would attest only itself.
  """

  def __init__(self, binary: pathlib.Path, attested: bool = True):
    self._binary = binary
    self._attested = attested

  def sign(
      self,
      report: pathlib.Path,
      model: dict[str, Any],
      predicate: pathlib.Path,
      out: pathlib.Path,
  ) -> None:
    """Binds the report and the model to a token naming this image."""
    command = [
        str(self._binary),
        f"--subject={report}",
        # Descriptive only: a verifier waives this and relies on the image
        # digest, which already covers the weights.
        f"--subject-digest={model['name']}={model['digest']}",
        f"--predicate-type={PREDICATE_TYPE}",
        f"--predicate={predicate}",
        f"--out={out}",
    ]
    if not self._attested:
      command.append("--no-attestation")
    subprocess.run(command, check=True)
