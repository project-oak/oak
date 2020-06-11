const fs = require('fs');
const protobufjs = require('protobufjs');
const grpc = require('@grpc/grpc-js');
const grpcProtoLoader = require('@grpc/proto-loader');

const CERT_PATH = __dirname + '/../../../certs/local/ca.pem';
const SERVICE_PROTO_PATH = __dirname + '/../../proto/hello_world.proto';
const OAK_LABEL_PROTO_PATH = __dirname + '/../../../../oak/proto/label.proto';

// Keep in sync with /oak/server/rust/oak_runtime/src/node/grpc/server/mod.rs.
const oakLabelGrpcMetadataKey = 'x-oak-label-bin';

async function main() {
  const [oaklabelDefinition, helloWorldDefinition] = await Promise.all([
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

  client.sayHello(
    { greeting: 'Node.js' },
    getGrpcMetadata(),
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
