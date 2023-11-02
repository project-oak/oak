//
// Copyright 2023 The Project Oak Authors
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

package com.google.oak.verification;

import java.nio.ByteBuffer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Optional;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class AmdAttestationReportTest {
  /**
   * Adapted from
   * https://docs.google.com/document/d/1oPA3cu9eRsiAASrQSqlW7r8Lns18Vvy9B_vYS3SzNLQ/edit?resourcekey=0-LKVkZ79qD30tZ-xmh041Ww
   */
  private static int[] AMD_ATTESTATION_REPORT = {
    /* version */ 0, 0, 0, 2,
    /* guest_svn */ 0, 0, 0, 0,
    // Guest policy is 8 bytes, see Table 9
    /* policy abi_minor */ 0,  
    /* policy abi_major */ 0,
    /* policy flags */ 3,
    /* policy _reserved */ 0, 0, 0, 0, 0,
    /* family_id */ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* image_id  */ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* vmpl */ 0, 0, 0, 0,
    /* signature_algo */ 0, 0, 0, 1,
    /* current_tcb boot_loader */ 2,
    /* current_tcb tee */ 0,
    /* current_tcb _reserved */ 0, 0, 0, 0,
    /* current_tcb snp */ 5,
    /* current_tcb microcode */ 68,
    /* platform_info cf. Table 23 mirror? */ 0, 0, 0, 0, 0, 0, 0, 1,
    /* reserved, signing_key, mask_chip_key, author_key_en */ 0, 0, 0, 0,
    /* reserved */ 0, 0, 0, 0,
    /* report_data */ 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* measurement */ 97, 211, 210, 230, 19, 186, 66, 233, 104, 130, 236, 109, 150, 119, 166, 58, 64, 176, 111, 219, 82, 100, 237, 219, 90, 17, 150, 254, 63, 55, 236, 169, 56, 156, 228, 227, 95, 56, 33, 147, 135, 230, 109, 159, 107, 82, 155, 60,
    /* host_data */ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* id_key_digest */ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* author_key_digest */ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* report_id */ 15, 185, 250, 73, 37, 235, 208, 14, 33, 1, 88, 215, 92, 151, 57, 172, 102, 183, 158, 126, 104, 31, 123, 98, 168, 203, 127, 167, 56, 46, 129, 65,
    /* report_id_ma */ 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    /* reported_tcb boot_loader */ 2,
    /* reported_tcb tee */ 0,
    /* reported_tcb _reserved */ 0, 0, 0, 0,
    /* reported_tcb snp */ 5,
    /* reported_tcb microcode */ 68,
    /* _reserved_0 */ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* chip_id */ 188, 78, 137, 48, 124, 236, 7, 183, 206, 16, 106, 45, 10, 9, 191, 140, 50, 131, 208, 104, 70, 29, 175, 165, 2, 190, 15, 192, 183, 46, 253, 187, 127, 173, 16, 120, 245, 157, 63, 46, 215, 195, 240, 145, 137, 71, 39, 1, 80, 154, 205, 26, 93, 145, 201, 21, 98, 18, 209, 198, 88, 81, 188, 250,
    /* committed_tcb boot_loader */ 2,
    /* committed_tcb tee */ 0,
    /* committed_tcb _reserved */ 0, 0, 0, 0,
    /* committed_tcb snp */ 5,
    /* committed_tcb microcode */ 68,
    /* current_build */ 3,
    /* current_minor */ 49,
    /* current_major */ 1,
    /* _reserved_1 */ 0,
    /* committed_build */ 3,
    /* committed_minor */ 49,
    /* committed_major */ 1,
    /* _reserved_2 */ 0,
    /* launch_tcb boot_loader */ 2,
    /* launch_tcb tee */ 0,
    /* launch_tcb _reserved */ 0, 0, 0, 0,
    /* launch_tcb snp */ 5,
    /* launch_tcb microcode */ 68,
    /* _reserved_3 */ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* signature r */ 191, 90, 127, 112, 158, 147, 184, 139, 109, 34, 212, 59, 117, 242, 95, 126, 212, 26, 148, 96, 217, 92, 10, 252, 6, 227, 56, 55, 181, 17, 175, 211, 78, 237, 206, 51, 184, 234, 80, 105, 103, 166, 72, 230, 224, 208, 70, 149, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* signature s */ 243, 5, 67, 117, 74, 168, 21, 2, 158, 187, 183, 162, 24, 197, 72, 149, 17, 199, 217, 178, 225, 168, 150, 113, 25, 43, 118, 11, 4, 70, 237, 38, 180, 128, 102, 184, 159, 52, 198, 2, 127, 235, 113, 205, 72, 112, 52, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    /* _reserved */ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  };
      
  private byte[] amdAttestationReportBytes;
  private AmdAttestationReport amdAttestationReport;

  @Before
  public void setUp() throws Exception {
    amdAttestationReportBytes = new byte[AMD_ATTESTATION_REPORT.length];
    for (int i = 0; i < AMD_ATTESTATION_REPORT.length; ++i) {
      amdAttestationReportBytes[i] = (byte) AMD_ATTESTATION_REPORT[i];
    }
    amdAttestationReport = new AmdAttestationReport(amdAttestationReportBytes);
  }

  @Test
  public void testLengthAsExpected() {
    Assert.assertEquals(0x4a0, AMD_ATTESTATION_REPORT.length);
  }

  @Test
  public void testVersion() {
    Assert.assertEquals(2, amdAttestationReport.getVersion());
  }

  @Test
  public void testReportData() {
    byte[] reportData = amdAttestationReport.getReportData();
    Assert.assertEquals(64, reportData.length);
    Assert.assertEquals(42, reportData[0]);
  }

  @Test
  public void testMeasurement() {
    byte[] measurement = amdAttestationReport.getMeasurement();
    Assert.assertEquals(48, measurement.length);
    Assert.assertEquals(97, measurement[0]);
  }

  @Test
  public void testCurrentMinor() {
    Assert.assertEquals(49, amdAttestationReport.getCurrentMinor());
  }

  @Test
  public void testParseSucceeds() {
    AmdAttestationReport report = new AmdAttestationReport(amdAttestationReportBytes);
  }
}
