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

const REPOSITORY_ROOT = `${__dirname}/../../../..`;
const CERT_PATH = `${REPOSITORY_ROOT}/examples/certs/local/ca.pem`;
const OAK_LABEL_PROTO_PATH = `${REPOSITORY_ROOT}/oak_abi/proto/label.proto`;
const SERVICE_PROTO_PATH = `${REPOSITORY_ROOT}/examples/hello_world/proto/hello_world.proto`;

// Keep in sync with /oak_runtime/src/node/grpc/server/mod.rs.
const oakLabelGrpcMetadataKey = 'x-oak-label-bin';

async function main() {
  const protos = await protobufjs.load([
    OAK_LABEL_PROTO_PATH,
    SERVICE_PROTO_PATH,
  ]);

  function getGrpcMetadata() {
    // TODO(#1097): move this into an SDK package to allow re-use.
    const oakLabel = protos.lookupType('oak.label.Label');

    // TODO(#1066): Use a more restrictive Label.
    const publicUntrustedLabel = oakLabel.create({});
    const encodedLabel = oakLabel.encode(publicUntrustedLabel).finish();

    const metaData = new grpc.Metadata();
    metaData.add(oakLabelGrpcMetadataKey, encodedLabel);

    return metaData;
  }

  const helloWorldService = protos.lookupService(
    'oak.examples.hello_world.HelloWorld'
  );
  const credentials = grpc.credentials.createSsl(fs.readFileSync(CERT_PATH));

  const grpcClient = new grpc.Client('localhost:8080', credentials);

  // protobufjs supports rpc services, but does not provide an underlying rpc
  // implementation. Hence a function implemnting gRPC requests is passed when
  // creating a client instance of for this service.
  // Ref: http://protobufjs.github.io/protobuf.js/rpc.Service.html#rpcImpl
  const helloWorld = helloWorldService.create(
    (method, requestData, callback) => {
      // Ref: https://grpc.github.io/grpc/node/grpc.Client.html#makeUnaryRequest
      grpcClient.makeUnaryRequest(
        `/oak.examples.hello_world.HelloWorld/${method.name}`,
        // Serializer and deserializer function required by grpc-js. protobufjs
        // already implements these, hence we just pass the data through.
        (requestData) => requestData,
        (responseData) => responseData,
        requestData,
        getGrpcMetadata(),
        callback
      );
    }
  );

  try {
    const response = await helloWorld.sayHello({ greeting: 'Node.js' });
    console.log(response.reply);
    process.exit(0);
  } catch (error) {
    console.error(error);
    process.exit(1);
  }
}

main();
