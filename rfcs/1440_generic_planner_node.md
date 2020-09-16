# RFC#1440: Configuration-based Generic Planner Node

## Objective

Make the node graph easier to set up, reason about and amenable to static
analysis.

## Background

An Oak application creates an initial node and calls the entry point on that
node. A typical pattern is to use this initial node as a "Planner Node",
responsible for creating all other nodes and channels. The creation of the nodes
and channels is done through code. For simple cases it is easy to figure out
what the graph can look like by inspecting the code, but it becomes increasingly
difficult as the complexity of the logic of the planner node increases to cope
with more complex node graphs. Another drawback of the code-based dynamic node
creation is that we have to run the code to use the introspection mechanism to
visualise the node graph.

Generating the node graph automatically based on a configuration/manifest file
should simplify this. It should be easier to figure out what the node graph will
look like through inspecting a manifest file (assuming it has an easily
understandable format). Additional benefits of configuration-based node creation
include:

- It would be easier to build tools to visualise the node graph without running
  the application.
- It would be easier to build tools to perform static analysis of the node graph
  to detect potential problems.
- It would usually be easier to reason about the security of a static node
  graph.

## Overview

Moving all node and channel creation to a configuration-based mechanism is a
significant and potentially disruptive change. This RFC proposes a more gradual
approach by implementing a re-usable Wasm-based planner node that uses a
manifest file to do the node and channel creation. The functionality can be
expanded over time to support more complex scenarios.

The planner node will be responsible for creating nodes, creating channels,
sending channel handles to the created nodes to ensure that the full node graph
is created on start-up. It will also act as a message router, which would route
HTTP- and GRPC invocations to other nodes based on the associated labels.

Some applications require dynamic creation of nodes and channels based on the
labels associated with incoming invocations. A sub-graph template mechanism will
be implemented to support dynamic node creation. The typical scenario where this
is required is the case where a per-user node must be created to support
per-user labels.

## Detailed Design

### Planner Node

The planner node will be the initial node created for an application. The
manifest file will be passed to the planner node as part of the application's
`ConfigMap`.

The planner node will create all the nodes and channels as specified with the
appropriate labels. It will send initialisation messages to each of the nodes,
providing additional configuration and handles to channels. It is the
responsibility of each of the nodes to store these channels for future
communications with other nodes. It will send a filtered version of the config
map as part of the initialisation message, based on the configuration keys
specified in the `config_files` field.

### Node and Channel Creation

Creation of static nodes and channels is straight-forward. The planner node will
read these on start-up and use the values specified in the manifest to create
the nodes and channels and send the read- and write handles to the appropriate
nodes.

Dynamic node creation will be supported by parameterised sub-graph templates.
The template will specify a label pattern to match. The pattern will include
information on extracting the parameter values from the incoming labels. The
trigger for dynamic node creation will be incoming invocations. The label of the
channel associated with the request receiver will be used to match the template
label pattern and extract the parameters.

A sub-graph template will also be able to define whether it is persistent or
not. If it is persistent, an instance will be created the first time it is
needed for a specific label. For future instances of the same label it will
reuse the already-created nodes and channels. If it is not persistent, the
subgraph will be recreated every time a matching label arrives. It is the
responsibility of the nodes in question to close the channels and terminate once
processing is complete to avoid running out of resources.

The template will contain definitions of nodes and channels to be created. These
definitions can use the parameters for specifying labels, names etc. The
template will support a formatting mechanism to replace placeholders with
parameter values. In most cases the parameter values will be byte arrays. The
formatting will allow specification of conversions to strings so that it could
be used in names etc. Initially only base64 encoding will be supported for
converting from bytes to strings.

As an example, if a parameter named `user_id` is extracted for the template, a
user-specific node can use the base64 encoding of the user id to create a unique
name:

```Toml
[node]
name = "user_{base64($user_id)}"
```

The initial impementation of dynamic node creation will focus only on support
for user labels, as it is the first motivating example we have. Each extracted
parameter will be the matching bytes that represent the user identity (currently
the HMAC of the bearer token, but in future it would be the user's public key).

### Invocation Routing

The planner node will be responsible for creating the required pseudo nodes as
well. In the specific cases of HTTP- and gRPC pseudo nodes each pseudo node will
send all invocations over a single dedicated invocation channel. The planner
node will, by default, have the handle to receive these invocations and
therefore be responsible for routing them to the right Wasm nodes based on the
associated labels (specifically the label associated with the request receiver
channel should match the label of the target Wasm node). Since it would be
possible for multiple Wasm nodes to share the same label, the planner node would
need an indication of which Wasm node should receive invocations with a specific
label on the request receiver channel.

If more advanced routing is required, the planner node could forward the
invocation receiver channel to another node that can do the routing. The problem
in this case is that the new node would have to be responsible for creating any
per-label nodes as well if these nodes must be dynamically created, seeing that
the planner node will no longer be able to see incoming invocations.

Questions:

- Would there be a requirement for multiple gRPC server pseudo nodes running on
  different ports to each have a different configuration for Invocation routing?
- Should we use special handling of channel types to determine the targets for
  routing, or should we mark specific nodes as targeted invocation receivers?
- Should we support overriding all routing so that the planner node still
  receives all invocations, but always forward it to a single specified node
  that is responsible for the routing?

### Manifest File

The manifest file will be passed to the application as part of the initial
configuration map as a TOML file. The assumption is that each application will
have one unique node graph manifest file, which will be maintained by the
developer of the application. The node graph manifest should be consistent with
the application configuration file and the defense-in-depth restrictions. As
part of the future work we plan on building analysis tools to validate that this
is the case.

The file will be deserialised into the following structure:

```rust

/// A static node definition.
struct Node {
  /// Unique name for the node.
  name: String,

  /// The label associated with the node.
  ///
  /// Note The `Label` type is the same type defined in label.proto.
  label: Label,

  /// The keys of the files from the config map that must be passed to the node
  /// as part of the initialisation message. This will be used to generate a
  /// filtered view of the map that will be sent as part of the initialisation
  /// message.
  config_files: Vec<String>,

  /// Whether this node should be the target node for all gRPC invocations
  /// targeted at the specified label. This is only used if the planner node is
  /// also responsible for invocation routing.
  ///
  /// Note: it should be validated that this value is only true for one node
  /// per label.
  grpc_invocation_receiver: bool,

  /// Whether this node should be the target node for all HTTP invocations
  /// targeted at the specified label. This is only used if the planner node is
  /// also responsible for invocation routing.
  ///
  /// Note: it should be validated that this value is only true for one node
  /// per label.
  http_invocation_receiver: bool,
}

/// A static channel definition.
struct Channel {
  /// Unique name of the channel.
  name: String,

  /// The label associated with the channel.
  label: Label,

  /// The name of the node that will receive the handle for the receiver half
  /// of the channel.
  ///
  /// Note: this is in anticipation of changing channels to a multi-producer,
  /// single-consumer model to resolve #1197.
  receiver_node: String,

  /// The names of nodes that will receive handles to the write-half of the
  /// channel.
  sender_nodes: Vec<String>,
}

/// A dyanimc node definition template.
struct NodeTemplate {
  /// Unique name for the node.
  name: String,

  /// The template for constructing the label associated with the node using
  /// the extracted paramters.
  label: LabelTemplate,

  /// The keys of the files from the config map that must be passed to the node
  /// as part of the initialisation message. This will be used to generate a
  /// filtered view of the map that will be sent as part of the initialisation
  /// message.
  config_files: Vec<String>,

  /// Whether this node should be the target node for all gRPC invocations
  /// targeted at the specified label. This is only used if the planner node is
  /// also responsible for invocation routing.
  ///
  /// Note: it should be validated that this value is only true for one node
  /// per label.
  grpc_invocation_receiver: bool,

  /// Whether this node should be the target node for all HTTP invocations
  /// targeted at the specified label. This is only used if the planner node is
  /// also responsible for invocation routing.
  ///
  /// Note: it should be validated that this value is only true for one node
  /// per label.
  http_invocation_receiver: bool,
}

/// A static channel definition.
struct ChannelTemplate {
  /// Unique name of the channel.
  name: String,

  /// The template for constructing the label associated with the channel using
  /// the extracted parameters.
  label: LabelTemplate,

  /// The name of the node that will receive the handle for the receiver half
  /// of the channel.
  ///
  /// Note: this is in anticipation of changing channels to a multi-producer,
  /// single-consumer model to resolve #1197.
  receiver_node: String,

  /// The names of nodes that will receive handles to the write-half of the
  /// channel.
  sender_nodes: Vec<String>,
}

/// A sub-graph template for dynamically creating nodes and channels based on
/// parameters extract from the label matching process.
struct Template {
  /// The template used for matching the label and extracting parameters.
  label: LabelTemplate,

  /// The template nodes to create.
  nodes: Vec<NodeTemplate>,

  /// The template channels to create.
  channels: Vec<ChannelTemplate>,
}

struct NodeGraph {
  /// The nodes that will be created.
  nodes: Vec<Node>,

  /// The channels that will be created.
  channels: Vec<Channel>,

  /// The per label sub-graph templates used for dynamic node creation.
  templates: Vec<Template>,
}



```

### Initialising New Nodes

After creating a new Wasm node the planner node will send an initialisation
message to the new node over the initial channel. These initialisation messages
will provide other channels and additional configuration files to the node in a
standard format. The additional configuration files will be a per-node filtered
view of the `ConfigMap` that was passed to the application on start-up.

Nodes should support multiple initialisation messages. This would be required if
per-label dynamic node and channel creation is supported. If a new dynamic
channel is created, one of the channel halves are likely to end up in an
existing node, and so would be passed in as an additional initialisation
message.

Question: if multiple initialisation messages are supported should we change it
to using `oneof` and send a separate initialisation message for the config map,
follow by one message for each sender and receiver channel?

```proto

message SenderChannelInfo {
  // The name of the channel for the handle.
  string channel_name = 1,

  // The Sender wrapping a write-half of the channel.
  // Question: How do we define message_type?
  oak.handle.Sender sender = 2;
}

message ReceiverChannelInfo {
  // The name of the channel for the handle.
  string channel_name = 1,

  // The Receiver wrapping the read-half of the channel.
  // Question: How do we define message_type?
  oak.handle.Receiver receiver = 2;
}

message NodeInitialisation {
  // The Senders that the node expects.
  repeated SenderChannelInfo senders = 1,

  // The Receivers that the node expects.
  repeated ReceiverChannelInfo receivers = 2,

  // A filtered map of config entries intended for the node.
  ConfigMap config = 3
}

```

### Accessing Channels

All the channels needed by a node will be passed as part of the initialisation
message. The channels are represented as repeating of `SenderChannelInfo`s and
`ReceiverChannelInfo`s. The keys for each will be the name of the channel. This
means that channels would need unique names in the manifest file. The downside
of this approach is that the code needs to be aware of the names of the channels
in the manifest file.

This is not ideal, but we could work around it by adding a mapping as a config
entry between internal names that the code understand and the channels names in
the manifest file. We can then use this to support modification of the manifest
file without having to recompile the Wasm nodes.

## Planning

The initial implementation will be done as a static `planner` example. It will
create multiple test nodes and channels and connect these together. The example
will also expose a gRPC method to the client so the client can request the
manifest file. The client will compare the manifest file to the introspection
data to test that the nodes were created as expected.

The next step would be to extend the planner node to support per-label dynamic
node creation. This will be used to implement an alternative version of the
private database example as a proof of concept for per-user node creation and
gRPC invocation routing.

Once the intial implementations are done, some of the common reusable code will
be moved to the SDK. The fist example of such reusable code is support for node
to accept an initial proto that contains a list of `Sender`s and `Receiver`s
that wrap the handles for channels that should be available to the node, and
potentially additional configuration files.

The next step would be to update the existing examples to reuse the
configuration-based `planner` node.

## Future Work

### Static analysis tools

We can support application developers in finding potential issues in their
applications through static analysis tools that can help detect common problems:

- Check for consistency between application configuration and node graph
  manifest
- Check that all node and channel names are unique
- Check that there is only one gRPC invocation receiver for each label
- Check that there is only one HTTP invocation receiver for each label
- Check that all nodes can write to handles they receive
- Check that all nodes can read from handles they receive
- Check that the node graph manifest does not violate defense-in-depth
  restritcions
- Hihglight points where data is declassified to `Public`
- Find nodes that can never receive data (unneeded nodes)
- Find nodes where data will get stuck (dead ends)
- Find risky patterns (e.g. diamond shaped graph with declassification in each
  path)

Note: The static analysis tools that focus on the structure of the node graph
will only be able to analyse the initial state. It is possible for nodes to send
channel handles to other nodes embedded in protobuf messages, which would mean
that additional connections might be created over time. Nodes could also close
channels and nodes could terminate. This means that while the initial setup
might be static it does not guarantee that the node structure will never change.

### Declaration of supported message types

Each node will be able to declare which protobuf message types it can read and
write. Each channel will be annotated with the single message type it is
intended for. If a channel should carry multiple message types, it can be done
using a wrapper message and `oneof`. This will allow us to build additional
static analysis tools to make sure each node can handle the messages it will
receive and all messages that it might send will go to a node that can
understand those messages.

We might consider making this part of the initial version:

- It could help with providing a strongly typed mechanism for sending the
  additional channels during initialisation
- It might allow us to automatically determine which channels are required
  without having to specify channels in the manifest
