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
const OAK_IDENTITY_PROTO_PATH = `${REPOSITORY_ROOT}/oak_abi/proto/identity.proto`;
const SERVICE_PROTO_PATH = `${REPOSITORY_ROOT}/examples/hello_world/proto/hello_world.proto`;

// Keep these in sync with /oak_abi/src/lib.rs
const OAK_LABEL_GRPC_METADATA_KEY = 'x-oak-label-bin';
const OAK_SIGNED_CHALLENGE_GRPC_METADATA_KEY =
  'x-oak-signed-auth-challenge-bin';

// Generated using the command:
// ```shell
// cargo run --manifest-path=oak_sign/Cargo.toml -- \
//     generate \
//     --private-key=http-test.key \
//     --public-key=http-test.pub
// ```
// TODO(#1859): Generate a key in JS, instead of hardcoding one.
const PUBLIC_KEY = Buffer.from(
  'i7g/Mgft/2hsZBGRd+MF4f+Eir2Iyamkch8l4vPgLac=',
  'base64'
);

// Generated using the command:
// ```shell
// cargo run --manifest-path=oak_sign/Cargo.toml -- \
//     sign \
//     --private-key=http-test.key \
//     --input-string="oak-challenge" \
//     --signature-file=http-test.sign
// ```
// TODO(#1859): Sign the hash in JS, instead of hardcoding this.
const SIGNED_HASH = Buffer.from(
  'ijbZOQ9mTtDEQyDEt+G3Rh0E0zwnY6+DkRd7bkllJINJbAhIiss3krdOzWo9d/iz5NJ9XGbp/qutOjAPSBkyDg==',
  'base64'
);

async function main() {
  const protos = await protobufjs.load([
    OAK_LABEL_PROTO_PATH,
    OAK_IDENTITY_PROTO_PATH,
    SERVICE_PROTO_PATH,
  ]);

  function getMetadata() {
    const metadata = new grpc.Metadata();

    // TODO(#1097): move this into an SDK package to allow re-use.
    const oakLabelType = protos.lookupType('oak.label.Label');
    // TODO(#1066): Use a more restrictive Label.
    const publicUntrustedLabel = oakLabelType.create({});
    const encodedLabel = oakLabelType.encode(publicUntrustedLabel).finish();
    metadata.set(OAK_LABEL_GRPC_METADATA_KEY, encodedLabel);

    const oakSignedChallengeType = protos.lookupType(
      'oak.identity.SignedChallenge'
    );
    const signedChallenge = oakSignedChallengeType.create({
      signedHash: SIGNED_HASH,
      publicKey: PUBLIC_KEY,
    });
    const encodedSignedChallenge = oakSignedChallengeType
      .encode(signedChallenge)
      .finish();
    metadata.set(
      OAK_SIGNED_CHALLENGE_GRPC_METADATA_KEY,
      encodedSignedChallenge
    );

    return metadata;
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
        getMetadata(),
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
