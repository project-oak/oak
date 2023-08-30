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

package com.google.oak.server;

import com.google.common.base.Preconditions;
import com.google.protobuf.InvalidProtocolBufferException;
import io.grpc.stub.StreamObserver;

/**
 * ConnectionAdapter encapsulates the following functional interfaces required for wrapping an
 * unencrypted bidirectional gRPC streaming method within an encrypted connection:
 *
 * <ul>
 *   <li>A ProtoParser for parsing decrypted message bytes into an instance of the request type
 *   <li>A ProtpSerializer for serializing instances of the response into a protobuf encoded byte
 *       array
 *   <li>A BidiConnection for invoking the inner service on the request stream
 *
 * @param <I> Type of the unencrypted requests
 * @param <O> Type of the unencrypted responses
 */
public final class ConnectionAdapter<I, O> {
  private final ProtoParser<I> inputParser;
  private final ProtoSerializer<O> outputSerializer;
  private final BidiConnection<I, O> connection;

  /**
   * Interface with a single method for parsing a protobuf encoded byte array into an instance of
   * type {@code I}. The conversion is successful if the input bytes protobuf encoding of an object
   * of type {@code I}. Otherwise an InvalidProtocolBufferException exception is thrown.
   */
  public interface ProtoParser<I> {
    /**
     * Parses the given bytes into an instance of {@code I}. The conversion is successful if the
     * input bytes are protobuf encoding of an object of type {@code I}. Otherwise an
     * InvalidProtocolBufferException exception is thrown.
     *
     * @param bytes protobuf encoded bytes to convert
     * @return an instance of {@code I}
     * @throws InvalidProtocolBufferException if input bytes cannot be interpreted as protobuf
     *     encoding of an instance of {@code I}.
     */
    I parse(byte[] bytes) throws InvalidProtocolBufferException;
  }

  /**
   * Interface with a single method for protobuf encoding of an object of type {@code O}.
   * @param <O> Type of the object to serialize
   */
  public interface ProtoSerializer<O> {
    /**
     * Serializes the given object into a protobuf encoded byte array.
     *
     * @param obj object to serialize
     * @return the resulting bytes
     */
    byte[] serialize(O obj);
  }

  /**
   * Interface with a single method representing a bidirectional gRPC streaming connection.
   *
   * @param <I> Type of the requests
   * @param <O> Type of the responses
   */
  public interface BidiConnection<I, O> {
    /**
     * Creates and returns a stream observer connected to the given {@code outboundStreamObserver}.
     * @param outboundStreamObserver StreamObserver for processing responses
     * @return StreamObserver for processing requests, connected to the {@code
     *     outboundStreamObserver}
     */
    StreamObserver<I> connect(StreamObserver<O> outboundStreamObserver);
  }

  public ConnectionAdapter(ProtoParser<I> inputParser, ProtoSerializer<O> outputSerializer,
      BidiConnection<I, O> connection) {
    this.inputParser = Preconditions.checkNotNull(inputParser);
    this.outputSerializer = Preconditions.checkNotNull(outputSerializer);
    this.connection = Preconditions.checkNotNull(connection);
  }

  /**
   * Creates and returns a stream observer, for processing message of type {@code I}, connected to
   * the given {@code outboundStreamObserver}.
   * @param outboundStreamObserver StreamObserver for processing  message of  type {@code O}
   * @return StreamObserver for processing message of  type {@code I}, connected to the {@code
   *     outboundStreamObserver}
   */
  public StreamObserver<I> connect(StreamObserver<O> outboundStreamObserver) {
    return connection.connect(outboundStreamObserver);
  }

  /**
   * Parses the given bytes into an instance of {@code I}. The conversion is successful if the
   * input bytes are protobuf encoding of an object of type {@code I}. Otherwise an
   * InvalidProtocolBufferException exception is thrown.
   *
   * @param bytes protobuf encoded bytes to convert
   * @return an instance of {@code I}
   * @throws InvalidProtocolBufferException if input bytes cannot be interpreted as protobuf
   *     encoding of an instance of {@code I}.
   */
  public I parse(byte[] bytes) throws InvalidProtocolBufferException {
    return inputParser.parse(bytes);
  }

  /**
   * Serializes the given object into a protobuf encoded byte array.
   *
   * @param obj object to serialize
   * @return the resulting bytes
   */
  public byte[] serialize(O obj) {
    return outputSerializer.serialize(obj);
  }
}
