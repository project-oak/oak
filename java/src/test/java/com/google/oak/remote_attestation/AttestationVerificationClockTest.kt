//
// Copyright 2025 The Project Oak Authors
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
package com.google.oak.remote_attestation

import kotlin.test.assertFailsWith
import org.junit.Assert.assertEquals
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

@RunWith(JUnit4::class)
class AttestationVerificationClockTest {
  class TestClock(var fakeTime: Long) : AttestationVerificationClock {
    override fun millisecondsSinceEpoch(): Long {
      return fakeTime
    }
  }

  class FakeException(msg: String) : RuntimeException(msg)

  class FailingClock : AttestationVerificationClock {
    override fun millisecondsSinceEpoch(): Long {
      throw FakeException("FAKE EXCEPTION")
    }
  }

  @Test
  fun rustClock_providesTimeInRust() {
    val fakeTime = 12345L
    val fakeTime2 = 6542345L
    val clock = TestClock(fakeTime)
    val rust_clock_ptr = newRustJniClock(clock)

    assertEquals(rustJniClockGetTime(rust_clock_ptr), fakeTime)

    clock.fakeTime = fakeTime2
    assertEquals(rustJniClockGetTime(rust_clock_ptr), fakeTime2)
  }

  @Test
  fun jniRustClock_forwardsExceptions() {
    val clock = FailingClock()
    val rust_clock_ptr = newRustJniClock(clock)
    assertFailsWith<FakeException>("FAKE EXCEPTION") { rustJniClockGetTime(rust_clock_ptr) }
  }

  private external fun newRustJniClock(clock: AttestationVerificationClock): Long

  private external fun rustJniClockGetTime(nativePtr: Long): Long

  companion object {
    init {
      System.loadLibrary("attestation_verification_clock_test_jni")
    }
  }
}
