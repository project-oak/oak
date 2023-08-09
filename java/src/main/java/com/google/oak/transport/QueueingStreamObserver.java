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

package com.google.oak.transport;

import static java.util.concurrent.TimeUnit.MILLISECONDS;

import io.grpc.Status;
import io.grpc.stub.StreamObserver;
import java.time.Duration;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * A thread-safe StreamObserver that queues received messages, so that they can
 * be picked from the
 * queue once needed.
 *
 * @param <T> Type of the message
 */
public final class QueueingStreamObserver<T> implements StreamObserver<T> {
  private static final Logger logger = Logger.getLogger(QueueingStreamObserver.class.getName());

  private final BlockingQueue<T> messages;

  public QueueingStreamObserver(int capacity) {
    this.messages = new LinkedBlockingQueue<>(capacity);
  }

  public QueueingStreamObserver() {
    this.messages = new LinkedBlockingQueue<>();
  }

  public T take() throws InterruptedException {
    return messages.take();
  }

  public T poll(Duration timeout) throws InterruptedException {
    return messages.poll(timeout.toMillis(), MILLISECONDS);
  }

  @Override
  public void onNext(T message) {
    try {
      messages.put(message);
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
      logger.log(Level.WARNING, "Queueing the server response was interrupted");
    }
  }

  @Override
  public void onError(Throwable error) {
    Status status = Status.fromThrowable(error);
    logger.log(Level.WARNING, "Couldn't receive a response: " + status);
  }

  @Override
  public void onCompleted() {
    logger.log(Level.INFO,
        "Server streaming completed. Number of remaining messages in the queue: %d",
        messages.size());
  }
}
