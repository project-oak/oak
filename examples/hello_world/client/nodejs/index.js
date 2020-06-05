const fs = require('fs');
const protoLoader = require('@grpc/proto-loader');
const grpc = require('@grpc/grpc-js');

const CERT_PATH = __dirname + '/../../../certs/local/ca.pem';
const PROTO_PAH = __dirname + '/../../proto/hello_world.proto';

const packageDefinition = protoLoader.loadSync(PROTO_PAH);
const helloWorldProto = grpc.loadPackageDefinition(packageDefinition).oak
  .examples.hello_world;
const credentials = grpc.credentials.createSsl(fs.readFileSync(CERT_PATH));

// TODO(#1066): Use a more restrictive Label.
const client = new helloWorldProto.HelloWorld('localhost:8080', credentials);

client.sayHello({ greeting: 'Node.js' }, (error, response) => {
  if (error) {
    console.error(error);
    process.exit(1);
  } else {
    console.log(response.reply);
  }
});

process.exit(0);
