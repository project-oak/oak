const fs = require('fs');
const protoLoader = require('@grpc/proto-loader');
const grpc = require('@grpc/grpc-js');

const CERT_PATH = __dirname + '/../../../certs/local/ca.pem';
const PROT_PAH = __dirname + '/../../proto/hello_world.proto';

const packageDefinition = protoLoader.loadSync(PROT_PAH);
const helloWorldProto = grpc.loadPackageDefinition(packageDefinition).oak
  .examples.hello_world;
const credentials = grpc.credentials.createSsl(fs.readFileSync(CERT_PATH));
const client = new helloWorldProto.HelloWorld('localhost:8080', credentials);

client.sayHello({ greeting: 'Node.js' }, (error, response) => {
  if (error) {
    console.error(error);
  } else {
    console.log(response.reply);
  }
});
