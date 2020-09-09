//
// Copyright 2020 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

import React from 'react';
import {
  OakApplicationState,
  ChannelHalfDirection,
  NodeId,
  ChannelID,
  AbiHandle,
} from '~/components/Root';

type StateGraphProps = {
  applicationState: OakApplicationState;
};

// Generate a Graphviz dot graph that shows the shape of the Nodes and Channels
function getGraphFromState(applicationState: OakApplicationState) {
  const getNodeDotId = (nodeId: NodeId) => `node${nodeId}`;
  const getChannelDotId = (channelId: ChannelID) => `channel${channelId}`;
  const getHandleDotId = (nodeId: NodeId, handle: AbiHandle) =>
    `node${nodeId}_${handle}`;

  const oakNodes = [...applicationState.nodeInfos.entries()].map(
    ([nodeId, nodeInfo]) => `${getNodeDotId(nodeId)} [label="${nodeInfo.name}"]`
  );
  const oakHandles = [...applicationState.nodeInfos.entries()]
    .map(([nodeId, nodeInfo]) =>
      [...nodeInfo.abiHandles.entries()].map(
        ([handle]) =>
          `${getHandleDotId(nodeId, handle)} [label="${nodeId}:${handle}"]`
      )
    )
    .flat();
  const oakChannels = [
    ...applicationState.channels.entries(),
  ].map(([channelId]) => getChannelDotId(channelId));
  const connections = [...applicationState.nodeInfos.entries()]
    .map(([nodeId, nodeInfo]) =>
      [...nodeInfo.abiHandles.entries()].map(([handle, channelHalf]) => {
        switch (channelHalf.direction) {
          case ChannelHalfDirection.Write:
            return `${getNodeDotId(nodeId)} -> ${getHandleDotId(
              nodeId,
              handle
            )} -> ${getChannelDotId(channelHalf.channelId)}`;

          case ChannelHalfDirection.Read:
            return `${getChannelDotId(
              channelHalf.channelId
            )} -> ${getHandleDotId(nodeId, handle)} -> ${getNodeDotId(nodeId)}`;

          default:
            // This should never happen
            throw new Error(
              `Encountered unhandled direction value ${channelHalf.direction}`
            );
        }
      })
    )
    .flat();

  return `digraph Runtime {
    {
      node [shape=box style=filled fillcolor=red fontsize=24]
      ${oakNodes.join('\n      ')}
    }
    {
      node [shape=hexagon style=filled fillcolor=orange]
      ${oakHandles.join('\n      ')}
    }
    {
      node [shape=ellipse style=filled fillcolor=green]
      ${oakChannels.join('\n      ')}
    }
    ${connections.join('\n    ')}
  }
  `;
}

export default function StateGraph({ applicationState }: StateGraphProps) {
  return (
    <section
      dangerouslySetInnerHTML={{
        __html: getGraphFromState(applicationState)
          .replace(/ /g, '&nbsp;')
          .replace(/\n/g, '<br/>'),
      }}
    ></section>
  );
}
