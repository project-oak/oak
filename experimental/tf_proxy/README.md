# Attested TensorFlow Proxy

This directory contains a proof-of-concept implementation of a remote
attestation proxy that connects to a
[TensorFlow model server](https://github.com/tensorflow/serving) instance. It
also contains a client to connect to the proxy and do inference against a model
hosted on the model server.

This example assumes that the TensorFlow model server binary is installed
locally. See
https://github.com/tensorflow/serving/blob/master/tensorflow_serving/g3doc/setup.md
for more information.

This example uses a saved model that was trained using the steps provided at
https://github.com/tensorflow/serving/blob/master/tensorflow_serving/g3doc/serving_basic.md

The proxy starts an instance of the TensorFlow model server with the provided
startup arguments. It implements the remote attestation protocol using streaming
gRPC similarly to the implementation in the Oak Functions runtime, allowing
clients to set up an end-to-end encrypted and attested channel. It then proxies
subsequent communications to the TensorFlow model server instance over a Unix
Domain Socket.

It assumes that every subsequent message is a binary-serialised instance of a
`PredictRequest` proto and will send back a binary-serialised `PredictResponse`.
See
https://github.com/tensorflow/serving/blob/master/tensorflow_serving/apis/predict.proto
for the proto definitions.

The client downloads MNIST test data for the trained model and caches it
locally. The client connects to the proxy and completes the remote attestation
handshake. It then runs inference tests on 100 of the test data items and
reports the error rate.
