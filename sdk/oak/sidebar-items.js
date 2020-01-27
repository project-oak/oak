initSidebarItems({"enum":[["ChannelReadStatus",""],["OakError","Generic Oak error."],["OakStatus","Generated files are compatible only with the same version of protobuf runtime."]],"fn":[["channel_close","Close the specified channel [`Handle`]."],["channel_create","Create a new unidirectional channel."],["channel_read","Read a message from a channel without blocking."],["channel_write","Write a message to a channel."],["node_create","Create a new Node running the configuration identified by `config_name`, running the entrypoint identified by `entrypoint_name` (for a Web Assembly Node), passing it the given handle."],["random_get","Fill a buffer with random data."],["result_from_status","Convert a status returned from a host function call to a `Result`."],["set_panic_hook","Install a panic hook that logs [panic information]."],["wait_on_channels","Wait for one or more of the provided handles to become ready for reading from.  On success, the returned vector of [`ChannelReadStatus`] values will be in 1-1 correspondence with the passed-in vector of [`Handle`]s."]],"mod":[["grpc","Functionality to help Oak Nodes interact with gRPC."],["io","Wrappers for Oak SDK types to allow their use with [`std::io`]."],["proto","Auto-generated code for processing protocol buffer message definitions and gRPC service definitions."],["rand","Functionality to allow use of the rand crate in Oak."],["storage","Helper library for accessing Oak storage services."]],"struct":[["Handle","Handle used to identify read or write channel halves."],["ReadHandle","Wrapper for a handle to the read half of a channel."],["WriteHandle","Wrapper for a handle to the send half of a channel."]]});