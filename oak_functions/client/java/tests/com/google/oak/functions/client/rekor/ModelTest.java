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

package com.google.oak.functions.client.rekor;

import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class ModelTest {
  @Test
  public void testUnmarshalRekorLogEntry() throws Exception {
    String logEntryPath = "oak_functions/client/testdata/logentry.json";

    String json = Files.readString(Path.of(logEntryPath));
    Model.LogEntry entry = Model.unmarshalLogEntry(json);
    Assert.assertTrue(entry.body.length() > 0);
    Assert.assertEquals(entry.logIndex, 1323526);
    Assert.assertEquals(entry.bodyObject.kind, "rekord");
    Assert.assertEquals(entry.bodyObject.spec.data.hash.algorithm, "sha256");
    Assert.assertEquals(entry.bodyObject.spec.signature.format, "x509");
  }
}
