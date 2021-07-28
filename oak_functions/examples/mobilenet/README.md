# Oak Functions `TensorFlow` example

This is an Oak Functions application that demonstrates the use of native
TensorFlow API for machine learning inference. The example uses the MobilenetV2
model and is based on
https://github.com/sonos/tract/tree/main/examples/tensorflow-mobilenet-v2.

## Configuration

The configuration for this example specifies the URL to a TensorFlow model on
Cloud Storage. This is the frozen TensorFlow MobilenetV2 model,
`mobilenet_v2_1.4_224_frozen.pb`. The entire model package can be obtained using
the following command:

```bash
wget https://storage.googleapis.com/mobilenet_v2/checkpoints/mobilenet_v2_1.4_224.tgz
```

## Request

The request from the client is expected to contain a `MobilenetImage` as
specified in `oak_functions/examples/mobilenet/proto/mobilenet.proto`. A
`MobilenetImage` contains an image as an RGB byte array, as well as the width
and height of the image. This information is needed to be able to reconstruct
the image, and resize it.

## Response

The response contains an `Inference` as specified in
`oak_functions/protos/abi/proto`. It consists of a vector of floats, and an
additional filed specifying the desired shape of the inference vector.
