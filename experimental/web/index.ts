import Vue from 'vue';
import VueMaterial from 'vue-material';
import oakAbiProto from './protoc_out/oak_abi/proto/oak_abi_pb';
import oakApplicationProto from './protoc_out/oak_abi/proto/application_pb';
import labelProto from './protoc_out/oak_abi/proto/label_pb';
import handleProto from './protoc_out/proto/handle_pb';
import grpcInvocationProto from './protoc_out/oak_services/proto/grpc_invocation_pb';
import grpcEncapProto from './protoc_out/oak_services/proto/grpc_encap_pb';
import httpInvocationProto from './protoc_out/oak_services/proto/http_invocation_pb';
import httpEncapProto from './protoc_out/oak_services/proto/http_encap_pb';
import logProto from './protoc_out/oak_services/proto/log_pb';
import treehouseProto from './protoc_out/experimental/treehouse/application/proto/treehouse_pb';
import treehouseInternalProto from './protoc_out/experimental/treehouse/application/proto/treehouse_init_pb';

type Message = {
  bytes: number[];
  handles: number[];
};

type Channel = {
  name: string;
  messages: Message[];
  callback?: (m: Message) => void;
};

Vue.use(VueMaterial);

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
    login: function (e: Event) {
      console.log('login');
    },
    // Read the specified file and load it as a Wasm module.
    readFile: function (e: Event) {
      const target = e.target as HTMLInputElement;
      const file = target.files![0];
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
    loadModule: async function (e: Event) {
      const contents = (<FileReader>e.target).result as ArrayBuffer;
      console.log('file loaded');
      this.module = await WebAssembly.compile(contents);
      this.exports = WebAssembly.Module.exports(this.module);
      this.imports = WebAssembly.Module.imports(this.module);
      await this.instantiate();
    },
    instantiate: async function () {
      // Lookup the types that we will use later on.
      const { NodeConfiguration } = oakApplicationProto;
      const { Label } = labelProto;
      const { OakStatus, ChannelReadStatus } = oakAbiProto;

      // Provide a mock implementation of some of the Oak ABI functions.
      // Mostly these just log their argument to the trace, and return a
      // successful status without actually doing anything.
      const importObject = {
        oak: {
          wait_on_channels: (buf: number, count: number) => {
            const status = OakStatus.OK;
            const bytes = this.readMemory(buf, (HANDLE_SIZE_BYTES + 1) * count);
            const entry = `${new Date().toISOString()}: wait_on_channels(${[
              buf,
              count,
            ].join(', ')}) -> ${status}
      bytes: [${bytes}]`;
            this.trace.push(entry);
            this.writeMemory(buf + 8, [ChannelReadStatus.READ_READY]);
            return status;
          },
          channel_close: (handle: number) => {
            const status = OakStatus.OK;
            const entry = `${new Date().toISOString()}: channel_close(${[
              handle,
            ].join(', ')}) -> ${status}`;
            this.trace.push(entry);
            return status;
          },
          channel_label_read: (
            handle: number,
            buf: number,
            size: number,
            actualSize: number
          ) => {
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
            handle: number,
            buf: number,
            size: number,
            actualSize: number,
            handleBuf: number,
            handleCount: number,
            actualHandleCount: number
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
            const handlesOut = message.handles.flatMap((v: number) => [
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
          channel_write: (
            handle: number,
            buf: number,
            size: number,
            handleBuf: number,
            handleCount: number
          ) => {
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
            const message: Message = {
              bytes: Array.from(bytes),
              handles: Array.from(handles),
            };
            const channel: Channel = this.channels[handle];
            if (channel.callback) {
              channel.callback(message);
            } else {
              console.log('no callback registered for channel ' + handle);
              // Hack to invoke HTTP request callback even if it is not registered yet.
              if (channel.name == 'HTTP request') {
                console.log('HTTP request hack');
                this.httpRequestCallback(BigInt(handle) + BigInt(1))(message);
              }
            }
            return status;
          },
          channel_write_with_downgrade: (
            handle: number,
            buf: number,
            size: number,
            handleBuf: number,
            handleCount: number
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
            writeHandle: number,
            readHandle: number,
            nameBuf: number,
            nameSize: number,
            labelBuf: number,
            labelSize: number
          ) => {
            const status = OakStatus.OK;
            const name = new TextDecoder().decode(
              this.readMemory(nameBuf, nameSize)
            );
            const label = Label.deserializeBinary(
              this.readMemory(labelBuf, labelSize)
            ).toObject();
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
            const newChannelHandle = this.createChannel(name);
            this.writeMemory(writeHandle, [newChannelHandle]);
            this.writeMemory(readHandle, [newChannelHandle]);
            return status;
          },
          channel_create_with_downgrade: (
            writeHandle: number,
            readHandle: number,
            nameBuf: number,
            nameSize: number,
            labelBuf: number,
            labelSize: number
          ) => {
            const status = OakStatus.OK;
            const name = new TextDecoder().decode(
              this.readMemory(nameBuf, nameSize)
            );
            const label = Label.deserializeBinary(
              this.readMemory(labelBuf, labelSize)
            ).toObject();
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
            nameBuf: number,
            nameSize: number,
            configBuf: number,
            configLen: number,
            labelBuf: number,
            labelSize: number,
            handle: number
          ) => {
            const status = OakStatus.OK;
            const name = new TextDecoder().decode(
              this.readMemory(nameBuf, nameSize)
            );
            const config = NodeConfiguration.deserializeBinary(
              this.readMemory(configBuf, configLen)
            ).toObject();
            const label = Label.deserializeBinary(
              this.readMemory(labelBuf, labelSize)
            ).toObject();
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
          random_get: (buf: number, len: number) => {
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
      this.instance = await WebAssembly.instantiate(this.module, importObject);
    },
    readMemory: function (offset: number, len: number): Uint8Array {
      return new Uint8Array(this.instance.exports.memory.buffer, offset, len);
    },
    writeMemory: function (offset: number, data: number[]) {
      console.log(`writing ${data.length} bytes to offset ${offset}: ${data}`);
      const a = new Uint8Array(
        this.instance.exports.memory.buffer,
        offset,
        data.length
      );
      data.forEach((v: number, i: number) => (a[i] = v));
    },
    // Invoke an exported function from the module.
    invoke: function (exportName: string) {
      console.log('invoking export: ' + exportName);

      this.createChannel('dummy');
      const logChannelHandle = this.createChannel('log', this.logCallback);
      const grpcInvocationReceiverHandle = this.createChannel(
        'grpc-invocations'
      );

      const grpcInvocation = new grpcInvocationProto.GrpcInvocation();
      const grpcResponseChannel = this.createChannel('grpc-response');
      const grpcRequestChannel = this.createChannel('grpc-request');
      const grpcRequest = new grpcEncapProto.GrpcRequest();
      {
        // https://github.com/project-oak/oak/blob/c2fb4a05f31e639c9f0499ebfd0aae18932f82f2/experimental/treehouse/application/proto/treehouse.proto#L42
        grpcRequest.setMethodName('/oak.examples.treehouse.Treehouse/GetCards');
        const getCardsRequest = new treehouseProto.GetCardsRequest();
        grpcRequest.setReqMsg(getCardsRequest.serializeBinary());
        grpcRequest.setLast(true);
      }
      const requestBytes = Array.from(grpcRequest.serializeBinary());
      (<Channel>this.channels[grpcRequestChannel]).messages.push({
        bytes: requestBytes,
        handles: [],
      });

      {
        const receiver = new handleProto.Receiver();
        receiver.setId(grpcRequestChannel);
        grpcInvocation.setReceiver(receiver);
      }
      {
        const sender = new handleProto.Sender();
        sender.setId(grpcResponseChannel);
        grpcInvocation.setSender(sender);
      }

      const httpInvocationChannel = this.createChannel(
        'http-invocations',
        this.httpInvocationCallback
      );

      const grpcInvocationBytes = Array.from(grpcInvocation.serializeBinary());
      console.log('gRPC invocation bytes', grpcInvocationBytes);
      this.channels[grpcInvocationReceiverHandle].messages.push({
        bytes: grpcInvocationBytes,
        handles: [grpcRequestChannel, grpcResponseChannel],
      });
      const initChannelHandle = this.createChannel('init');
      const init = new treehouseInternalProto.TreehouseHandlerInit();
      {
        const logSender = new handleProto.Sender();
        logSender.setId(logChannelHandle);
        init.setLogSender(logSender);
        const httpInvocationSender = new handleProto.Sender();
        httpInvocationSender.setId(httpInvocationChannel);
        init.setHttpInvocationSender(httpInvocationSender);
      }
      const bytes = Array.from(init.serializeBinary());
      console.log(`message bytes: ${bytes}`);
      this.channels[initChannelHandle].messages.push({
        bytes: bytes,
        handles: [
          grpcInvocationReceiverHandle,
          logChannelHandle,
          httpInvocationChannel,
        ],
      });
      // Oak entrypoints expect the handle of a channel from which to read
      // messages as a parameter, so we just pass a zero value here.
      const result = this.instance.exports[exportName](
        BigInt(initChannelHandle)
      );
      console.log('invocation result: ' + result);
    },
    createNode: function (
      config: oakApplicationProto.NodeConfiguration.AsObject
    ) {
      // TODO(#1067): Create mock nodes that replicate the functionality from the Oak
      // Runtime.
      console.log('creating node', config);
    },
    createChannel: function (name: string, callback?: (m: Message) => void) {
      const channelHandle =
        this.channels.push({
          name: name,
          messages: [],
          callback: callback,
        } as Channel) - 1;
      return channelHandle;
    },

    logCallback: function (m: Message) {
      const decoded = logProto.LogMessage.deserializeBinary(
        new Uint8Array(m.bytes)
      );
      console.log('LOG', decoded.toString());
    },

    httpInvocationCallback: function (m: Message) {
      const decoded = httpInvocationProto.HttpInvocation.deserializeBinary(
        new Uint8Array(m.bytes)
      );
      const httpRequestChannel = m.handles[0];
      const httpResponseChannel = m.handles[1];
      (<Channel>(
        this.channels[httpRequestChannel]
      )).callback = this.httpRequestCallback(httpResponseChannel);
      console.log('HTTP invocation', decoded);
    },

    httpRequestCallback: function (responseChannel: number) {
      return (m: Message) => {
        const decoded = httpEncapProto.HttpRequest.deserializeBinary(
          new Uint8Array(m.bytes)
        );

        if (
          ![
            'https://www.googleapis.com/calendar/v3/calendars/primary/events',
          ].includes(decoded.getUri())
        ) {
          console.log('forbidden HTTP request', decoded);
          return;
        }

        console.log('allowed HTTP request', decoded);

        const req = new XMLHttpRequest();
        req.open(decoded.getMethod(), decoded.getUri());
        // TODO: Find proper way of getting token.
        const GoogleAuth: any = (<any>window).GoogleAuth;
        const token = GoogleAuth.currentUser.get().getAuthResponse()
          .access_token;
        req.setRequestHeader('Authorization', 'Bearer ' + token);
        req.send(decoded.getBody());

        const resp = new httpEncapProto.HttpResponse();
        resp.setStatus(req.status);
        resp.setBody(req.response);

        console.log('writing response to channel ', responseChannel);
        (<Channel>this.channels[responseChannel]).messages.push({
          bytes: Array.from(resp.serializeBinary()),
          handles: [],
        } as Message);
      };
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
