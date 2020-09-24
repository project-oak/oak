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
import { graphviz } from 'd3-graphviz';
import { transition } from 'd3-transition';
import { easeLinear } from 'd3-ease';
import { makeStyles } from '@material-ui/core/styles';
import {
  OakApplicationState,
  ChannelHalfDirection,
  NodeId,
  ChannelID,
  AbiHandle,
} from '~/components/Root';

// Generate a Graphviz dot graph that shows the shape of the Nodes and Channels
function getGraphFromState(applicationState: OakApplicationState) {
  const getNodeDotId = (nodeId: NodeId) => `node${nodeId.toString()}`;
  const getChannelDotId = (channelId: ChannelID) =>
    `channel${channelId.toString()}`;
  const getHandleDotId = (nodeId: NodeId, handle: AbiHandle) =>
    `node${nodeId.toString()}_${handle.toString()}`;
  const getMessageDotId = (channelId: ChannelID, messageIndex: number) =>
    `msg${channelId.toString()}_${messageIndex}`;

  const oakNodes = [...applicationState.nodeInfos.entries()].map(
    ([nodeId, nodeInfo]) =>
      `${getNodeDotId(nodeId)} [label="${
        nodeInfo.name
      }"  URL="/dynamic/node/${nodeId}"]`
  );
  const oakHandles = [...applicationState.nodeInfos.entries()]
    .map(([nodeId, nodeInfo]) =>
      [...nodeInfo.abiHandles.entries()].map(
        ([handle]) =>
          `${getHandleDotId(
            nodeId,
            handle
          )} [label="${nodeId}:${handle}" URL="/dynamic/node/${nodeId}/${handle}"]`
      )
    )
    .flat();
  const oakChannels = [...applicationState.channels.entries()].map(
    ([channelId]) =>
      `${getChannelDotId(channelId)} [URL="/dynamic/channel/${channelId}"]`
  );
  const oakMessages = [
    ...applicationState.channels.entries(),
  ].map(([channelId, channel]) =>
    channel.messages.map((message, index) => getMessageDotId(channelId, index))
  );
  const connections = [
    // Connections between nodes, handles, & channels
    ...[...applicationState.nodeInfos.entries()]
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
              )} -> ${getHandleDotId(nodeId, handle)} -> ${getNodeDotId(
                nodeId
              )}`;

            default:
              // This should never happen
              throw new Error(
                `Encountered unhandled direction value ${channelHalf.direction}`
              );
          }
        })
      )
      .flat(),
    // Connections between channels & messages
    'edge [arrowhead=none]',
    ...[...applicationState.channels.entries()].map(([channelId, channel]) =>
      channel.messages.map((message, index) =>
        index === 0
          ? // Connect the first message to the channel
            `${getMessageDotId(channelId, index)} -> ${getChannelDotId(
              channelId
            )}`
          : // Connect subsequent messages to the previous message
            `${getMessageDotId(channelId, index)} -> ${getMessageDotId(
              channelId,
              index - 1
            )}`
      )
    ),
  ];

  return `digraph Runtime {
    graph [bgcolor=transparent]
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
    {
      node [shape=rect fontsize=10 label="msg"]
      ${oakMessages.join('\n      ')}
    }
    ${connections.join('\n    ')}
  }
  `;
}

type StateGraphProps = {
  applicationState: OakApplicationState;
};

const useStyles = makeStyles(() => ({
  root: {
    width: '100%',
    height: '100%',

    '& > svg': { width: '100%', height: '100%' },
  },
}));

export default function StateGraph({ applicationState }: StateGraphProps) {
  const classes = useStyles();
  const ref = React.useRef<HTMLDivElement>(null);
  React.useEffect(() => {
    const dotGraph = getGraphFromState(applicationState);
    // Type as any to fix type mismatch caused by incorrect typings.
    const transiton: any = transition().duration(300).ease(easeLinear);
    graphviz(ref.current).transition(transiton).scale(0.9).renderDot(dotGraph);
  }, [applicationState]);

  return <div className={classes.root} ref={ref} />;
}
