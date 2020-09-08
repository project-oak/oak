# RFC#1440: Configuration-based Generic Planner Node

## Objective

Make the node graph easier to set up, reason about and amenable to static
analysis.

## Background

An Oak application creates an initial node and calls the entry point on that
node. A typical pattern is to use this initial node as a "Planner Node",
responsible for creating all other nodes and channels. The creation of the nodes
an channels is done through code. For simple cases it is easy to figure out what
the graph can look like by inspecting the code, but it becomes increasingly
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
- It would usualy be easier to reason about the security of a static node graph.

Moving all node and channel creation to a configuration-based mechanism is a
significant and potentially disruptive change. This RFC proposes a more gradual
approach by implementing a re-usable WASM-based planner node that uses a
manifest file to do the node and channel creation. The functionality can be
expanded over time to support more complex scenarios.

## Overview

The

## Detailed Design

### Planner node

### Manifest File

### Initialising New Nodes

### Accessing Channels

## Planning

The initial implementation will be done as a `planner` example. It will create
multiple test nodes and channels and connect these together. The example will
also expose a gRPC method to the client so the client can request the manifest
file. The client will compare the manifest file to the introspection data to
test that the nodes were created as expected.

Once the intial implementation is done, some of the common reusable code will be
moved to the SDK. The fist example of such reusable code is support for node to
accept an `init` proto that contains a list of `Sender`s and `Receiver`s that
wrap the handles for channels that should be available to the node.

The next step would be to update the existing examples to reuse the
configuration-based `planner` node.

## Future Work

### Static analysis tools

### Dynamic sub-graph creation

### Declaration of supported message types
