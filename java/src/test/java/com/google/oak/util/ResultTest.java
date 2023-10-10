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

package com.google.oak.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import java.util.concurrent.atomic.AtomicInteger;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class ResultTest {
  private static final String ERR_MSG = "error!";

  @Test
  public void testSuccess() {
    Result<Integer, String> success = Result.success(1);
    assertTrue(success.isSuccess());
    assertEquals(1, success.success().get().intValue());
    assertTrue(success.error().isEmpty());
  }

  @Test
  public void testError() {
    Result<Integer, String> error = Result.error(ERR_MSG);
    assertTrue(error.isError());
    assertEquals(ERR_MSG, error.error().get());
    assertTrue(error.success().isEmpty());
  }

  @Test
  public void testOrElseForSuccess() {
    int value = Result.success(1).orElse(2);
    assertEquals(1, value);
  }

  @Test
  public void testOrElseForError() {
    int value = (Integer) Result.error("error").orElse(2);
    assertEquals(2, value);
  }

  @Test
  public void testIfSuccessForSuccess() {
    AtomicInteger value = new AtomicInteger(0);
    Result.success(1).ifSuccess(value::set);
    assertEquals(1, value.get());
  }

  @Test
  public void testIfSuccessForError() {
    AtomicInteger value = new AtomicInteger(0);
    Result.error("error").ifSuccess(o -> value.set((Integer) o));
    assertEquals(0, value.get());
  }

  @Test
  public void testIfErrorForSuccess() {
    AtomicInteger value = new AtomicInteger();
    Result.success(1).ifError(o -> value.set((Integer) o));
    assertEquals(0, value.get());
  }

  @Test
  public void testIfErrorForError() {
    AtomicInteger value = new AtomicInteger(0);
    Result.error(2).ifError(value::set);
    assertEquals(2, value.get());
  }

  @Test
  public void testMapForSuccess() {
    Result<Integer, String> success = Result.success(1);
    Result<Integer, String> result = success.map(val -> val * 2);
    assertTrue(result.isSuccess());
    assertEquals(2, result.success().get().intValue());
    assertTrue(result.error().isEmpty());
  }

  @Test
  public void testMapForError() {
    Result<Integer, String> error = Result.error(ERR_MSG);
    Result<Integer, String> result = error.map(val -> val * 2);
    assertTrue(result.isError());
    assertEquals(ERR_MSG, result.error().get());
    assertTrue(result.success().isEmpty());
  }

  @Test
  public void testMapErrorForSuccess() {
    Result<Integer, String> success = Result.success(1);
    Result<Integer, Integer> result = success.mapError(val -> val.length());
    assertTrue(result.isSuccess());
    assertEquals(1, result.success().get().intValue());
    assertTrue(result.error().isEmpty());
  }

  @Test
  public void testMapErrorForError() {
    Result<Integer, String> error = Result.error(ERR_MSG);
    Result<Integer, Integer> result = error.mapError(val -> val.length());
    assertTrue(result.isError());
    assertEquals(ERR_MSG.length(), result.error().get().intValue());
    assertTrue(result.success().isEmpty());
  }

  @Test
  public void testAndThenForSuccessToSuccess() {
    Result<Integer, String> success = Result.success(1);
    Result<Integer, String> result = success.andThen(val -> Result.success(val));
    assertTrue(result.isSuccess());
    assertEquals(1, result.success().get().intValue());
    assertTrue(result.error().isEmpty());
  }

  @Test
  public void testAndThenForSuccessToError() {
    Result<Integer, String> success = Result.success(1);
    Result<Integer, String> result = success.andThen(val -> Result.error(ERR_MSG));
    assertTrue(result.isError());
    assertEquals(ERR_MSG, result.error().get());
    assertTrue(result.success().isEmpty());
  }

  @Test
  public void testAndThenForErrorToSuccess() {
    Result<Integer, String> error = Result.error(ERR_MSG);
    Result<Integer, String> result = error.andThen(val -> Result.success(1));
    assertTrue(result.isError());
    assertEquals(ERR_MSG, result.error().get());
    assertTrue(result.success().isEmpty());
  }

  @Test
  public void testAndThenForErrorToError() {
    Result<Integer, String> error = Result.error(ERR_MSG);
    Result<Integer, String> result = error.andThen(val -> Result.error(ERR_MSG + ERR_MSG));
    assertTrue(result.isError());
    assertEquals(ERR_MSG, result.error().get());
    assertTrue(result.success().isEmpty());
  }

  @Test
  public void testMergeSuccessAndSuccess() {
    Result<Integer, String> first = Result.success(1);
    Result<Integer, String> second = Result.success(2);

    Result<Integer, String> result = Result.merge(first, second, (f, s) -> f + s);
    assertTrue(result.isSuccess());
    assertEquals(3, result.success().get().intValue());
    assertTrue(result.error().isEmpty());
  }

  @Test
  public void testMergeSuccessAndError() {
    Result<Integer, String> first = Result.success(1);
    Result<Integer, String> second = Result.error(ERR_MSG);

    Result<Integer, String> result = Result.merge(first, second, (f, s) -> f + s);
    assertTrue(result.isError());
    assertEquals(ERR_MSG, result.error().get());
    assertTrue(result.success().isEmpty());
  }

  @Test
  public void testMergeErrorAndError() {
    Result<Integer, String> first = Result.error(ERR_MSG);
    Result<Integer, String> second = Result.error(ERR_MSG + ERR_MSG);

    Result<Integer, String> result = Result.merge(first, second, (f, s) -> f + s);
    assertTrue(result.isError());
    assertEquals(ERR_MSG, result.error().get());
    assertTrue(result.success().isEmpty());
  }

  @Test
  public void testUnwrapError() {
    Result<Integer, String> error = Result.error(ERR_MSG);
    assertTrue(error.isError());
    RuntimeException e = assertThrows(
        RuntimeException.class, () -> { Integer unused = error.unwrap("Expecting error"); });
    assertEquals(String.format("Expecting error: %s", ERR_MSG), e.getMessage());
  }

  @Test
  public void testUnwrapSuccess() {
    Result<String, String> success = Result.success("1");
    assertEquals("1", success.unwrap("No error!"));
  }
}
