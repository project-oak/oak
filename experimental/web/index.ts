import Vue from 'vue';
import oakAbiProto from './protoc_out/oak_abi/proto/oak_abi_pb';

declare const protobuf: any;

function init() {
  const HANDLE_SIZE_BYTES = 8;
  const app = new Vue({
    el: '#app',
    data: {
      // Exports of the loaded Module.
      exports: [],
      // Import of the loaded Module.
      imports: [],
      // Oak ABI calls trace.
      trace: [],
      // Created channels.
      channels: [],
      // Loaded module.
      module: null,
      // Loaded module instance.
      instance: null,
      // Protobuf definitions.
      protobuf: null,
    },
    methods: {
      // Read the specified file and load it as a Wasm module.
      readFile: function (e) {
        const file = e.target.files[0];
        if (!file) {
          console.log('no file selected');
          return;
        }
        const reader = new FileReader();
        reader.onload = this.loadModule;
        reader.readAsArrayBuffer(file);
      },
      // Parse the provided ArrayBuffer as a Wasm module and load it as an Oak module,
      // providing the necessary imports.
      loadModule: async function (e) {
        const contents = e.target.result;
        console.log('file loaded');
        this.module = await WebAssembly.compile(contents);
        this.exports = WebAssembly.Module.exports(this.module);
        this.imports = WebAssembly.Module.imports(this.module);
        await this.instantiate();
      },
      instantiate: async function () {
        // Load proto files from GitHub. We cannot refer to local files unless they are served
        // via a web server first.
        // This means that if protobuf definitions are modified locally, this script will not
        // be able to use the updated definitions.
        this.protobuf = await protobuf.load([
          'https://raw.githubusercontent.com/project-oak/oak/main/oak_abi/proto/application.proto',
          'https://raw.githubusercontent.com/project-oak/oak/main/oak_abi/proto/label.proto',
          'https://raw.githubusercontent.com/project-oak/oak/main/oak_abi/proto/oak_abi.proto',
          // 'https://raw.githubusercontent.com/project-oak/oak/main/proto/handle.proto',
          // 'https://raw.githubusercontent.com/project-oak/oak/main/oak_services/proto/grpc_invocation.proto',
          // 'https://raw.githubusercontent.com/project-oak/oak/main/oak_services/proto/log.proto',
          // 'https://raw.githubusercontent.com/project-oak/oak/main/examples/hello_world/proto/hello_world_internal.proto',
        ]);

        // Lookup the types that we will use later on.
        const NodeConfiguration = this.protobuf.lookupType(
          'oak.application.NodeConfiguration'
        );
        const Label = this.protobuf.lookupType('oak.label.Label');
        const { OakStatus } = oakAbiProto;
        const ChannelReadStatus = this.protobuf.lookupEnum(
          'oak_abi.ChannelReadStatus'
        );

        // Provide a mock implementation of some of the Oak ABI functions.
        // Mostly these just log their argument to the trace, and return a
        // successful status without actually doing anything.
        const importObject = {
          oak: {
            wait_on_channels: (buf, count) => {
              const status = OakStatus.OK;
              const bytes = this.readMemory(
                buf,
                (HANDLE_SIZE_BYTES + 1) * count
              );
              const entry = `${new Date().toISOString()}: wait_on_channels(${[
                buf,
                count,
              ].join(', ')}) -> ${status}
      bytes: [${bytes}]`;
              this.trace.push(entry);
              this.writeMemory(buf + 8, [ChannelReadStatus.values.READ_READY]);
              return status;
            },
            channel_close: (handle) => {
              const status = OakStatus.OK;
              const entry = `${new Date().toISOString()}: channel_close(${[
                handle,
              ].join(', ')}) -> ${status}`;
              this.trace.push(entry);
              return status;
            },
            channel_label_read: (handle, buf, size, actualSize) => {
              const status = OakStatus.OK;
              const entry = `${new Date().toISOString()}: channel_label_read(${[
                handle,
                buf,
                size,
                actualSize,
              ].join(', ')}) -> ${status}`;
              this.trace.push(entry);
              return status;
            },
            channel_read: (
              handle,
              buf,
              size,
              actualSize,
              handleBuf,
              handleCount,
              actualHandleCount
            ) => {
              const status = OakStatus.OK;
              const entry = `${new Date().toISOString()}: channel_read(${[
                handle,
                buf,
                size,
                actualSize,
                handleBuf,
                handleCount,
                actualHandleCount,
              ].join(', ')}) -> ${status}`;
              this.trace.push(entry);
              const channel = this.channels[handle];
              console.log(`${handle} -> ${channel.name}`);
              const messages = channel.messages;
              console.log(`${messages.length} messages available`);
              const message = messages.shift();

              console.log(`channel_read() -> ${JSON.stringify(message)}`);

              const bytesOut = message.bytes;
              console.log('bytes', bytesOut);
              this.writeMemory(buf, bytesOut);
              const actualSizeOut = [bytesOut.length, 0, 0, 0];
              console.log('actualSize', actualSizeOut);
              this.writeMemory(actualSize, actualSizeOut);
              // Hacky way of converting to 64bit representation. Only works for small values of v.
              const handlesOut = message.handles.flatMap((v) => [
                v,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
              ]);
              console.log('handles', handlesOut);
              this.writeMemory(handleBuf, handlesOut);
              const handleSizeOut = [message.handles.length, 0, 0, 0];
              console.log('handle size', handleSizeOut);
              this.writeMemory(actualHandleCount, handleSizeOut);
              return status;
            },
            channel_write: (handle, buf, size, handleBuf, handleCount) => {
              const status = OakStatus.OK;
              const bytes = this.readMemory(buf, size);
              const bytesString = new TextDecoder().decode(bytes);
              const handles = new Uint8Array(
                this.instance.exports.memory.buffer,
                handleBuf,
                handleCount
              );
              const entry = `${new Date().toISOString()}: channel_write(${[
                handle,
                buf,
                size,
                handleBuf,
                handleCount,
              ].join(', ')}) -> ${status}
      bytes: [${bytes}]
      bytes(string): "${bytesString}"
      handles: [${handles}]`;
              this.trace.push(entry);
              return status;
            },
            channel_write_with_downgrade: (
              handle,
              buf,
              size,
              handleBuf,
              handleCount
            ) => {
              const status = OakStatus.OK;
              const bytes = this.readMemory(buf, size);
              const bytesString = new TextDecoder().decode(bytes);
              const handles = new Uint8Array(
                this.instance.exports.memory.buffer,
                handleBuf,
                handleCount
              );
              const entry = `${new Date().toISOString()}: channel_write_with_downgrade(${[
                handle,
                buf,
                size,
                handleBuf,
                handleCount,
              ].join(', ')}) -> ${status}
      bytes: [${bytes}]
      bytes(string): "${bytesString}"
      handles: [${handles}]`;
              this.trace.push(entry);
              return status;
            },
            channel_create: (
              writeHandle,
              readHandle,
              nameBuf,
              nameSize,
              labelBuf,
              labelSize
            ) => {
              const status = OakStatus.OK;
              const name = new TextDecoder().decode(
                this.readMemory(nameBuf, nameSize)
              );
              const label = Label.decode(this.readMemory(labelBuf, labelSize));
              const entry = `${new Date().toISOString()}: channel_create(${[
                writeHandle,
                readHandle,
                nameBuf,
                nameSize,
                labelBuf,
                labelSize,
              ].join(', ')}) -> ${status}
      name: ${JSON.stringify(name)}
      label: ${JSON.stringify(label)}`;
              this.trace.push(entry);
              return status;
            },
            channel_create_with_downgrade: (
              writeHandle,
              readHandle,
              nameBuf,
              nameSize,
              labelBuf,
              labelSize
            ) => {
              const status = OakStatus.OK;
              const name = new TextDecoder().decode(
                this.readMemory(nameBuf, nameSize)
              );
              const label = Label.decode(this.readMemory(labelBuf, labelSize));
              const entry = `${new Date().toISOString()}: channel_create_with_downgrade(${[
                writeHandle,
                readHandle,
                nameBuf,
                nameSize,
                labelBuf,
                labelSize,
              ].join(', ')}) -> ${status}
      name: ${JSON.stringify(name)}
      label: ${JSON.stringify(label)}`;
              this.trace.push(entry);
              return status;
            },
            node_create: (
              nameBuf,
              nameSize,
              configBuf,
              configLen,
              labelBuf,
              labelSize,
              handle
            ) => {
              const status = OakStatus.OK;
              const name = new TextDecoder().decode(
                this.readMemory(nameBuf, nameSize)
              );
              const config = NodeConfiguration.decode(
                this.readMemory(configBuf, configLen)
              );
              const label = Label.decode(this.readMemory(labelBuf, labelSize));
              const entry = `${new Date().toISOString()}: node_create(${[
                nameBuf,
                nameSize,
                configBuf,
                configLen,
                labelBuf,
                labelSize,
                handle,
              ].join(', ')}) -> ${status}
      name: ${JSON.stringify(name)}
      config: ${JSON.stringify(config)}
      label: ${JSON.stringify(label)}`;
              this.trace.push(entry);
              this.createNode(config);
              return status;
            },
            random_get: (buf, len) => {
              const status = OakStatus.OK;
              const entry = `${new Date().toISOString()}: random_get(${[
                buf,
                len,
              ].join(', ')}) -> ${status}`;
              this.trace.push(entry);
              return status;
            },
          },
        };
        this.instance = await WebAssembly.instantiate(
          this.module,
          importObject
        );
      },
      readMemory: function (offset, len) {
        return new Uint8Array(this.instance.exports.memory.buffer, offset, len);
      },
      writeMemory: function (offset, data) {
        console.log(
          `writing ${data.length} bytes to offset ${offset}: ${data}`
        );
        const a = new Uint8Array(
          this.instance.exports.memory.buffer,
          offset,
          data.length
        );
        data.forEach((v, i) => (a[i] = v));
      },
      // Invoke an exported function from the module.
      invoke: function (exportName) {
        console.log('invoking export: ' + exportName);

        // Manually build protobuf types.
        // https://github.com/project-oak/oak/blob/main/proto/handle.proto
        const HandleWrapper = new protobuf.Type('HandleWrapper').add(
          new protobuf.Field('handle', 1, 'fixed64')
        );
        this.protobuf.add(HandleWrapper);
        // https://github.com/project-oak/oak/blob/main/oak_services/proto/grpc_invocation.proto.
        const Invocation = new protobuf.Type('Invocation')
          .add(new protobuf.Field('receiver', 1, 'HandleWrapper'))
          .add(new protobuf.Field('sender', 2, 'HandleWrapper'));
        this.protobuf.add(Invocation);
        // https://github.com/project-oak/oak/blob/main/examples/hello_world/proto/hello_world_internal.proto
        const HelloWorldInit = new protobuf.Type('Init')
          .add(new protobuf.Field('logSender', 1, 'HandleWrapper'))
          .add(new protobuf.Field('translatorSender', 2, 'HandleWrapper'));
        this.protobuf.add(HelloWorldInit);

        this.createChannel('dummy');
        const logChannelHandle = this.createChannel('log');
        const grpcInvocationReceiverHandle = this.createChannel(
          'grpc-invocations'
        );
        const requestChannel = this.createChannel('request');
        const responseChannel = this.createChannel('response');
        const invocation = Invocation.create({
          receiver: {
            handle: requestChannel,
          },
          sender: {
            handle: responseChannel,
          },
        });
        const invocationBytes = Array.from(
          Invocation.encode(invocation).finish()
        );
        console.log('invocation bytes', invocationBytes);
        this.channels[grpcInvocationReceiverHandle].messages.push({
          bytes: invocationBytes,
          handles: [requestChannel, responseChannel],
        });
        const initChannelHandle = this.createChannel('init');
        const init = HelloWorldInit.create({
          logSender: {
            handle: logChannelHandle,
          },
        });
        const bytes = Array.from(HelloWorldInit.encode(init).finish());
        console.log(`message bytes: ${bytes}`);
        this.channels[initChannelHandle].messages.push({
          bytes: bytes,
          handles: [grpcInvocationReceiverHandle, logChannelHandle],
        });
        // Oak entrypoints expect the handle of a channel from which to read
        // messages as a parameter, so we just pass a zero value here.
        const result = this.instance.exports[exportName](
          BigInt(initChannelHandle)
        );
        console.log('invocation result: ' + result);
      },
      createNode: function (config) {
        // TODO(#1067): Create mock nodes that replicate the functionality from the Oak
        // Runtime.
        console.log('creating node', config);
      },
      createChannel: function (name) {
        const channelHandle =
          this.channels.push({ name: name, messages: [] }) - 1;
        return channelHandle;
      },
      // Reset the current Wasm instance and trace, but keep the module loaded, so
      // that we can perform another invocation from scratch.
      reset: function () {
        this.trace = [];
        this.instance = null;
        // Keep `this.module` set.
        this.instantiate();
      },
    },
  });
}
init();
