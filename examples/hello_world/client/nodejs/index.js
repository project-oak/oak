/*
 * Copyright 2019 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

const fs = require('fs');
const protobufjs = require('protobufjs');
const grpc = require('@grpc/grpc-js');
const grpcProtoLoader = require('@grpc/proto-loader');

const REPOSITORY_ROOT = `${__dirname}/../../../..`;
const CERT_PATH = `${REPOSITORY_ROOT}/examples/certs/local/ca.pem`;
const OAK_LABEL_PROTO_PATH = `${REPOSITORY_ROOT}/oak_abi/proto/label.proto`;
const SERVICE_PROTO_PATH = `${REPOSITORY_ROOT}/examples/hello_world/proto/hello_world.proto`;

// Keep in sync with /oak_runtime/src/node/grpc/server/mod.rs.
const oakLabelGrpcMetadataKey = 'x-oak-label-bin';

async function main() {
  const [oaklabelDefinition, helloWorldDefinition] = await Promise.all([
    // We use two different libs with a similar APIs to load proto files,
    // which due to the design of the `@grpc/grpc-js` lib.
    // `@grpc/proto-loader` is a wrapper around `protobufjs` that adds
    // functionality required for working with `grpc-js`, but omits others.
    // Hence we use grpcProtoLoader for gRPC services, and protobufjs
    // for all other protos.
    protobufjs.load(OAK_LABEL_PROTO_PATH),
    grpcProtoLoader.load(SERVICE_PROTO_PATH),
  ]);

  function getGrpcMetadata() {
    // TODO(#1097): move this into an SDK package to allow re-use.
    const OakLabel = oaklabelDefinition.lookupType('oak.label.Label');

    // TODO(#1066): Use a more restrictive Label.
    const publicUntrustedLabel = OakLabel.create({});
    const encodedLabel = OakLabel.encode(publicUntrustedLabel).finish();

    const metaData = new grpc.Metadata();
    metaData.add(oakLabelGrpcMetadataKey, encodedLabel);

    return metaData;
  }

  const helloWorldProto = grpc.loadPackageDefinition(helloWorldDefinition).oak
    .examples.hello_world;
  const credentials = grpc.credentials.createSsl(fs.readFileSync(CERT_PATH));

  const client = new helloWorldProto.HelloWorld('localhost:8080', credentials);

  // For documentation on client calls see the `@grpc/grpc-js` documentation:
  // https://grpc.github.io/grpc/node/grpc.Client.html#~CallProperties
  client.sayHello(
    // The arguments passed to the gRPC service. Corresponds to the
    // `HelloRequest` message type in hello_world.proto file.
    { greeting: 'Node.js' },
    // The metadata for this gRPC call.
    getGrpcMetadata(),
    // Callback invoked with the response.
    (error, response) => {
      if (error) {
        console.error(error);
        process.exit(1);
      } else {
        console.log(response.reply);
        process.exit(0);
      }
    }
  );
}

main();
