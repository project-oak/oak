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

import java.util.Objects;
import java.util.Optional;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Class {@code Result} is a generic class representing the result of an
 * operation that could either succeed and produce an instance of {@code R}, or
 * fail and produce an error of type {@code E}. An instance of {@code Result}
 * can encapsulate both outcomes.
 *
 * <p>
 * The main invariant that instances of this class maintain is that each object
 * either
 * contains a nonnull success value or a nonnull error value.
 */
public class Result<R, E> {
  private final Optional<R> success;
  private final Optional<E> error;

  /**
   * Create and return an instance of {@code Result<E, R>} wrapping
   * {@code success}
   * as the success value.
   *
   * @param success nonnull success value
   * @return a {@code Result} containing a success value
   */
  public static <R, E> Result<R, E> success(final R success) {
    Objects.requireNonNull(success);
    return new Result<R, E>(success, null);
  }

  /**
   * Create and return an instance of {@code Result<E, R>} wrapping {@code error}
   * as the error value.
   *
   * @param error nonnull error value
   * @return a {@code Result} containing an error value
   */
  public static <R, E> Result<R, E> error(final E error) {
    Objects.requireNonNull(error);
    return new Result<R, E>(null, error);
  }

  /**
   *
   * @return true if this object represents a success value, and false otherwise
   */
  public boolean isSuccess() {
    return success.isPresent();
  }

  /**
   * @return true if this object contains an error value, and false otherwise
   */
  public boolean isError() {
    return error.isPresent();
  }

  /**
   * Wraps the success value in this {@code Result} instance as a potentially
   * empty Optional. This
   * is guaranteed to return a non-empty Optional if {@code isSuccess()} returns
   * true.
   *
   * @return the success value wrapped in an Optional.
   */
  public Optional<R> success() {
    return Optional.ofNullable(success.orElse(null));
  }

  /**
   * Wraps the error value in this {@code Result} instance as a potentially empty
   * Optional. This
   * is guaranteed to return a non-empty Optional if {@code isError()} returns
   * true.
   *
   * @return the error value wrapped in an Optional
   */
  public Optional<E> error() {
    return Optional.ofNullable(error.orElse(null));
  }

  /**
   * Unwraps and returns the success value, if one is present, or the given
   * default.
   *
   * @param other nonnull default value
   * @return the success value, if one is present, or the given default value.
   */
  public R orElse(final R other) {
    return success.orElse(other);
  }

  /**
   * If a success value is present, invoke the specified consumer with the success
   * value, otherwise do nothing.
   *
   * @param consumer block to be executed if a success value is present
   * @throws NullPointerException if success value is present and consumer is null
   */
  public void ifSuccess(Consumer<R> consumer) {
    success.ifPresent(consumer);
  }

  /**
   * If there is an error, invoke the specified consumer with the error value,
   * otherwise do nothing.
   *
   * @param consumer block to be executed if an error value is present
   * @throws NullPointerException if this is an error and consumer is null
   */
  public void ifError(Consumer<E> consumer) {
    error.ifPresent(consumer);
  }

  /**
   * Maps a {@code Result<R, E>} to {@code Result<T, E>} by applying the input
   * {@code function} to
   * the contained success value, if one is present. This leaves the error value
   * untouched. This
   * function can be used to compose the results of two functions.
   *
   * @param <T>      the new success value type
   * @param function the function to apply to the success value
   * @return the transformed result of type {@code Result<T, E>}
   */
  public <T> Result<T, E> map(final Function<R, T> function) {
    return isSuccess() ? success(function.apply(success.get())) : error(error.get());
  }

  /**
   * Maps a {@code Result<R, E>} to {@code Result<R, T>} by applying the input
   * {@code function} to
   * the contained error value, if one is present. This leaves the success value
   * untouched. This
   * function can be used to pass through a successful value while handling an
   * error.
   *
   * @param <T>      the new error type
   * @param function the function to apply to the error value
   * @return the transformed result of type {@code Result<R, T>}
   */
  public <T> Result<R, T> mapError(final Function<E, T> function) {
    return isError() ? error(function.apply(error.get())) : success(success.get());
  }

  /**
   * Applies {@code function} on the success value, if one is present, and
   * flattens the result.
   * Otherwise, returns a {@code Result} containing the error value.
   *
   * <p>
   * This function can be used for composing operations that themselves return a
   * {@code Result}.
   *
   * @param <T>      the new success value type
   * @param function the function to apply to the success value
   * @return the flattened result of applying {@code function} to this
   *         {@code Result} instance
   */
  public <T> Result<T, E> andThen(final Function<R, Result<T, E>> function) {
    Result<Result<T, E>, E> result = map(function);
    return result.isSuccess() ? result.success.get() : error(result.error.get());
  }

  /**
   * Unwraps and returns the success value in this Result, if one is present.
   * Otherwise throws an UnwrapException containing the given error message.
   *
   * @param message the error message to include in the exception
   * @return the success value, if present
   * @throws UnwrapException containing the given error message, if the success
   *                         value in not
   *                         present in the Result
   */
  public R unwrap(String message) throws UnwrapException {
    if (isSuccess()) {
      return success().get();
    }
    throw new UnwrapException(String.format("%s: %s", message, error().get()));
  }

  /**
   * Merges the success values of two instances of {@code Result} by applying
   * {@code function} on
   * them. The input {@code Result} instances must have the same error type.
   *
   * <p>
   * If {@code first} is an error its error content will be returned, otherwise
   * the error
   * content of {@code second} will be returned. If neither {@code first} nor
   * {@code second}
   * contains an error, the result of applying {@code function} on their success
   * values will be
   * returned as a success value.
   *
   * @param <R> type of the success value in {@code first}
   * @param <T> type of the success value in {@code second}
   * @param <U> type of the success value of the output
   * @param <E> type of the error value
   * @return the result of merging {@code first} and {@code second} as described
   *         above
   */
  public static <R, T, U, E> Result<U, E> merge(
      final Result<R, E> first, final Result<T, E> second, BiFunction<R, T, U> function) {
    return first.andThen(f -> second.map(s -> function.apply(f, s)));
  }

  // Private constructor to disallow creation of instances that could violate the
  // invariant of this
  // class.
  private Result(R success, E error) {
    if (success != null && error != null) {
      // This should never happen, since this constructor is private and we only call
      // it in the functions of this class, which never set both `result` and `error`.
      throw new IllegalArgumentException();
    }

    this.success = Optional.ofNullable(success);
    this.error = Optional.ofNullable(error);
  }
}
