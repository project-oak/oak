# Attested TensorFlow Proxy

This directory contains a proof-of-concept implementation of a remote
atteststaion proxy that connects to a TensorFlow serving instance. It also
contains a client to connect to the proxy and do inference against a model.

This example assumes that the TensorFlow Model Server binary is installed. See
https://github.com/tensorflow/serving/blob/master/tensorflow_serving/g3doc/setup.md
for more information.

This example uses a saved model that was trained using the steps provided at
https://github.com/tensorflow/serving/blob/master/tensorflow_serving/g3doc/serving_basic.md

The proxy starts an instance of the TensorFlow model server with the provided
startup arguments. It uses the same remote attestation protocol that is
implemented by the Oak Functions runtime, allowing clients to set up an
end-to-end encrypted and attested channel. It then proxies subsequent
communications to the TensorFlow model server instance over a Unix Domain
Socket.

It assumes that every subsequent message is a binary-serialised instance of a
`PredictRequest` proto and will send back a binary-serialised `PredictResponse`.
See
https://github.com/tensorflow/serving/blob/master/tensorflow_serving/apis/predict.proto
for the proto definitions.
