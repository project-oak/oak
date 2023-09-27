//
// Copyright 2022 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

package com.google.oak.transparency;

import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class RekorLogEntryTest {
  private static final String LOG_ENTRY_PATH = "oak_remote_attestation_verification/testdata/logentry.json";

  @Test
  public void testCreate() throws Exception {
    String json = Files.readString(Path.of(LOG_ENTRY_PATH));
    RekorLogEntry r = RekorLogEntry.createFromJson(json);
    Assert.assertTrue(r.hasVerification());
    Assert.assertTrue(r.logEntry.body.length() > 0);
    Assert.assertEquals(r.logEntry.logIndex, 30891523);
    Assert.assertEquals(r.logEntry.bodyObject.kind, "rekord");
    Assert.assertEquals(r.logEntry.bodyObject.spec.data.hash.algorithm, "sha256");
    Assert.assertEquals(r.logEntry.bodyObject.spec.signature.format, "x509");
  }
}
