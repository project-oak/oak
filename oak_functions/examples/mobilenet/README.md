# Oak Functions `TensorFlow` example

This is an Oak Functions application that demonstrates the use of native
TensorFlow API for machine learning inference. The example uses the MobilenetV2
model and is based on
https://github.com/sonos/tract/tree/main/examples/tensorflow-mobilenet-v2.

In this example, we use the project Oak logo as input to the model. MobilenetV2
categorizes this image as a shield (label #789) with a confidence of about 0.18.

This examples requires the `oak-unsafe` feature to be enabled. This is specified
in `oak_functions/examples/mobilenet/example.toml`.

## Configuration

The configuration of this example specifies the path to a local TensorFlow file
containing the frozen MobilenetV2 model, `mobilenet_v2_1.4_224_frozen.pb`. The
entire model package can be obtained using the following command:

```shell
wget https://storage.googleapis.com/mobilenet_v2/checkpoints/mobilenet_v2_1.4_224.tgz
```

## Request

The request from the client is expected to contain an RGB image, as a byte array
that can be reshaped into a tensor of the shape specified in
`oak_functions/examples/mobilenet/config.toml`.

## Response

The response contains an `Inference` as specified in
`oak_functions/protos/abi/proto`. It consists of a vector of floats, and an
additional field specifying the shape of the inference vector.
