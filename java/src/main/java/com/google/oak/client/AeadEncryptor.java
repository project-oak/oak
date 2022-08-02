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

package com.google.oak.client;

import com.google.oak.client.Encryptor;
import com.google.oak.util.Result;
import java.io.IOException;
import java.security.GeneralSecurityException;

// TODO(#3066): Merge this with com.google.oak.remote_attestation.AeadEncryptor.
public class AeadEncryptor implements Encryptor {
  private final com.google.oak.remote_attestation.AeadEncryptor inner;

  public AeadEncryptor(final com.google.oak.remote_attestation.AeadEncryptor inner) {
    this.inner = inner;
  }

  @Override
  public Result<byte[], Exception> decrypt(final byte[] data) {
    try {
      return Result.success(inner.decrypt(data));
    } catch (GeneralSecurityException | IOException e) {
      return Result.error(e);
    }
  }

  @Override
  public Result<byte[], Exception> encrypt(final byte[] data) {
    try {
      return Result.success(inner.encrypt(data));
    } catch (GeneralSecurityException | IOException e) {
      return Result.error(e);
    }
  }
}
