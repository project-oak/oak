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
import java.util.Arrays;

class TcbVersion {
  public static final int SERIALIZED_SIZE = 8;

  TcbVersion(byte[] serialized) {
    bootLoader = serialized[0];
    tee = serialized[1];
    snp = serialized[6];
    microcode = serialized[7];
  }

  public int bootLoader;
  public int tee;
  public int snp;
  public int microcode;
}

/**
 * Provides read-access to AMD attestation report.
 *
 * For specification see Table 22 in
 * https://www.amd.com/content/dam/amd/en/documents/epyc-technical-docs/specifications/56860.pdf
 */
public class AmdAttestationReport {
  public AmdAttestationReport() {
    this.bytes = new byte[0x4a0];
  }

  public AmdAttestationReport(byte[] bytes) {
    this.bytes = bytes;
  }

  public int getVersion() {
    return getInt32(0x000);
  }

  public int getGuestSvn() {
    return getInt32(0x004);
  }

  public byte[] getFamilyId() {
    return getSlice(0x010, 16);
  }

  public byte[] getImageId() {
    return getSlice(0x020, 16);
  }

  public TcbVersion getCurrentTcb() {
    return new TcbVersion(getSlice(0x038, TcbVersion.SERIALIZED_SIZE));
  }

  public byte[] getReportData() {
    return getSlice(0x050, 0x040);
  }

  public byte[] getMeasurement() {
    return getSlice(0x090, 0x030);
  }

  public byte[] getHostData() {
    return getSlice(0x0c0, 0x020);
  }

  public byte[] getIdKeyDigest() {
    return getSlice(0x0e0, 0x030);
  }

  public byte[] getAuthorKeyDigest() {
    return getSlice(0x110, 0x030);
  }

  public byte[] getReportId() {
    return getSlice(0x140, 0x020);
  }

  public byte[] getReportIdMa() {
    return getSlice(0x160, 0x020);
  }

  public TcbVersion getReportedTcb() {
    return new TcbVersion(getSlice(0x0180, TcbVersion.SERIALIZED_SIZE));
  }

  public byte[] getChipId() {
    return getSlice(0x01a0, 0x040);
  }

  public TcbVersion getCommittedTcb() {
    return new TcbVersion(getSlice(0x01e0, TcbVersion.SERIALIZED_SIZE));
  }

  public int getCurrentBuild() {
    return getUInt8(0x1e8);
  }

  public int getCurrentMinor() {
    return getUInt8(0x1e9);
  }

  public int getCurrentMajor() {
    return getUInt8(0x1ea);
  }

  public int getCommittedBuild() {
    return getUInt8(0x1ec);
  }

  public int getCommittedMinor() {
    return getUInt8(0x1ed);
  }

  public int getCommittedMajor() {
    return getUInt8(0x1ee);
  }

  public TcbVersion getLaunchTcb() {
    return new TcbVersion(getSlice(0x1f0, TcbVersion.SERIALIZED_SIZE));
  }

  public byte[] getSignature() {
    return getSlice(0x02a0, 0x200);
  }

  private int getUInt8(int offset) {
    return (int) bytes[offset];
  }

  private int getInt32(int offset) {
    ByteBuffer buffer = ByteBuffer.wrap(bytes, offset, 4);
    return buffer.getInt();
  }

  private byte[] getSlice(int offset, int length) {
    return Arrays.copyOfRange(bytes, offset, offset + length);
  }

  private final byte[] bytes;
}
