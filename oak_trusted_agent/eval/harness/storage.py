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

"""Uploads signed evaluation bundles to Google Cloud Storage."""

import dataclasses
import os
import pathlib
import urllib.parse

from google.cloud import storage

# Confidential Space containers use external DNS (8.8.8.8), which cannot
# resolve metadata.google.internal. Default google-auth to the universal GCE
# link-local metadata IP so workload service account credentials work out of
# the box on any GCP VM.
os.environ.setdefault("GCE_METADATA_HOST", "169.254.169.254")


@dataclasses.dataclass(frozen=True)
class GcsStorage:
  """Uploads evaluation artifacts to a Google Cloud Storage bucket."""

  bucket: str
  prefix: str = ""

  @classmethod
  def from_uri(cls, uri: str) -> "GcsStorage":
    parsed = urllib.parse.urlparse(uri)
    if parsed.scheme != "gs" or not parsed.netloc:
      raise ValueError(f"expected gs://<bucket>[/<prefix>], got {uri!r}")
    return cls(bucket=parsed.netloc, prefix=parsed.path.strip("/"))

  def upload_dir(self, local_dir: pathlib.Path, subdir: str = "") -> str:
    """Uploads all files in local_dir to gs://<bucket>/<prefix>/<subdir>/."""
    client = storage.Client()
    bucket = client.bucket(self.bucket)
    dest_prefix = "/".join(filter(None, [self.prefix, subdir]))
    for path in sorted(local_dir.iterdir()):
      if path.is_file():
        blob_name = f"{dest_prefix}/{path.name}" if dest_prefix else path.name
        bucket.blob(blob_name).upload_from_filename(str(path))
    return f"gs://{self.bucket}/{dest_prefix}"
