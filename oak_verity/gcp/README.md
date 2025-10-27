# Oak Verity GCP

## Deploy

```bash
./oak_verity/deploy.sh
```

It will print something like

```text
instance_external_ip = "136.118.27.185"
instance_id = "8330022119405937896"
instance_name = "oak-verity-test"
instance_network_ip = "10.138.15.227"
instance_self_link = "https://www.googleapis.com/compute/v1/projects/oak-examples-477357/zones/us-west1-b/instances/oak-verity-test"
```

Note down the external IP address.

## Invoke

```bash
bazel build //oak_functions/examples/echo:echo
cp bazel-bin/oak_functions/examples/echo/echo.wasm /tmp/echo.wasm
```

```bash
echo 'hello' > /tmp/input.txt

bazel run oak_verity/grpc/client:oak_verity_grpc_client -- \
  --server-address=http://136.118.27.185:8080 \
  --wasm-module=/tmp/echo.wasm \
  --input-data=/tmp/input.txt \
  --output-data=/tmp/output.txt \
  --output-response=/tmp/response.binpb
```

```bash
protoc --decode=oak.verity.ExecuteResponse \
  proto/oak_verity/oak_verity.proto \
  < /tmp/response.binpb
```

Example decoded Assertion in CyberChef: <http://shortn/_q1T565xCfW>
