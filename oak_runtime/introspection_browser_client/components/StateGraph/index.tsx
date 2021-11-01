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
import { useHistory } from 'react-router-dom';
import { graphviz, Graphviz } from 'd3-graphviz';
import { transition } from 'd3-transition';
import { easeLinear } from 'd3-ease';
import FormGroup from '@material-ui/core/FormGroup';
import FormControlLabel from '@material-ui/core/FormControlLabel';
import Switch from '@material-ui/core/Switch';
import { makeStyles } from '@material-ui/core/styles';
import {
  OakApplicationState,
  ChannelHalfDirection,
  NodeId,
  ChannelID,
  AbiHandle,
} from '~/components/Root';

// Generate a Graphviz dot graph that shows the shape of the Nodes and Channels
function getGraphFromState(
  applicationState: OakApplicationState,
  options = {
    shouldIncludeHandles: false,
  }
) {
  const getNodeDotId = (nodeId: NodeId) => `node${nodeId}`;
  const getChannelDotId = (channelId: ChannelID) => `channel${channelId}`;
  const getHandleDotId = (nodeId: NodeId, handle: AbiHandle) =>
    `node${nodeId}_${handle}`;
  const getMessageDotId = (channelId: ChannelID, messageIndex: number) =>
    `msg${channelId}_${messageIndex}`;

  const oakNodes = [...applicationState.nodeInfos.entries()].map(
    ([nodeId, nodeInfo]) =>
      `${getNodeDotId(nodeId)} [label="${
        nodeInfo.name
      }"  URL="/dynamic/node/${nodeId}"]`
  );
  const oakHandles = options.shouldIncludeHandles
    ? [...applicationState.nodeInfos.entries()]
        .map(([nodeId, nodeInfo]) =>
          [...nodeInfo.abiHandles.entries()].map(
            ([handle, { direction, channelId }]) => {
              const shape =
                direction === ChannelHalfDirection.Write ? 'invhouse' : 'house';
              return `${getHandleDotId(
                nodeId,
                handle
              )} [shape="${shape}" label="${
                direction === ChannelHalfDirection.Write
                  ? 'writes to'
                  : 'reads from'
              } channel ${channelId}\n${handle}" URL="/dynamic/node/${nodeId}/${handle}"]`;
            }
          )
        )
        .flat()
    : [];
  const oakChannels = [...applicationState.channels.entries()].map(
    ([channelId, { name }]) =>
      `${getChannelDotId(
        channelId
      )} [URL="/dynamic/channel/${channelId}" label="${name}"]`
  );
  const oakMessages = [...applicationState.channels.entries()].map(
    ([channelId, channel]) =>
      channel.messages.map((message, index) =>
        getMessageDotId(channelId, index)
      )
  );
  const connections = [
    'edge [arrowsize=1.2 penwidth=5 color="#595959"]',
    // Connections between nodes, handles, & channels
    ...[...applicationState.nodeInfos.entries()]
      .map(([nodeId, nodeInfo]) =>
        [...nodeInfo.abiHandles.entries()].map(([handle, channelHalf]) => {
          switch (channelHalf.direction) {
            case ChannelHalfDirection.Write:
              return options.shouldIncludeHandles
                ? `${getNodeDotId(nodeId)} -> ${getHandleDotId(
                    nodeId,
                    handle
                  )} -> ${getChannelDotId(channelHalf.channelId)}`
                : `${getNodeDotId(nodeId)} -> ${getChannelDotId(
                    channelHalf.channelId
                  )} [edgeURL="/dynamic/node/${nodeId}/${handle}" edgetooltip="Write handle ${nodeId}:${handle}"]`;

            case ChannelHalfDirection.Read:
              return options.shouldIncludeHandles
                ? `${getChannelDotId(
                    channelHalf.channelId
                  )} -> ${getHandleDotId(nodeId, handle)} -> ${getNodeDotId(
                    nodeId
                  )}`
                : `${getChannelDotId(channelHalf.channelId)} -> ${getNodeDotId(
                    nodeId
                  )} [edgeURL="/dynamic/node/${nodeId}/${handle}" edgetooltip="Read handle ${nodeId}:${handle}"]`;

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
    'edge [arrowhead=none penwidth=2]',
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
    graph [bgcolor=transparent splines=ortho pad=0.5]
    {
      node [shape="box" style="filled" penwidth=0 margin=0.2 fillcolor="#3a3a3a" fontcolor="#faf8f8" fontsize=24 fontname="helvetica"]
      ${oakNodes.join('\n      ')}
    }
    {
      node [shape="hexagon" style="filled" penwidth=0 margin=0.02 fillcolor="#efa087" fontname="helvetica"]
      ${oakHandles.join('\n      ')}
    }
    {
      node [shape="box" style="filled" penwidth=0 margin=0.1 fillcolor="#3e7ea0" fontcolor="#faf8f8" fontsize=24 fontname="helvetica"]
      ${oakChannels.join('\n      ')}
    }
    {
      node [shape="rect" fontsize=10 label="msg" fontname="helvetica"]
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
    flexGrow: 1,
    position: 'relative',
  },

  graph: {
    width: '100%',
    height: '100%',

    '& > svg': { width: '100%', height: '100%' },
    '& > svg text': { fontFamily: 'inherit' },
  },

  formRow: {
    position: 'absolute',
    top: '10px',
    left: '10px',
    backgroundColor: 'rgba(255, 255, 255, 0.75)',
    borderRadius: '5px',
    backdropFilter: 'blur(5px)',
    padding: '4px 10px',
  },
}));

export default function StateGraph({ applicationState }: StateGraphProps) {
  const [shouldIncludeHandles, setShouldIncludeHandles] = React.useState(false);
  const classes = useStyles();
  const ref = React.useRef<HTMLDivElement>(null);
  const history = useHistory();
  React.useEffect(() => {
    async function drawGraph() {
      const dotGraph = getGraphFromState(applicationState, {
        shouldIncludeHandles,
      });
      let dot: Graphviz<any, any, any, any> | undefined;
      // Wrap graphviz in a promise to ensure that the graph is generated
      // prior to applying any transitions.
      await new Promise<void>((resolve) => {
        dot = graphviz(ref.current).dot(dotGraph, resolve);
      });
      const transiton = transition('ease').duration(300).ease(easeLinear);
      await new Promise<void>((resolve) => {
        dot!.transition(() => transiton).render(resolve);
      });
      // Get html links and convert them to client side redirects. This
      // prevents page reloads, preserving graph zoom-level etc.
      ref.current!.querySelectorAll('a').forEach((link) => {
        const href = link.getAttribute('href');
        const routePrefix = '/dynamic';

        if (href !== undefined && href!.startsWith(routePrefix)) {
          link.onclick = (event) => {
            event.preventDefault();
            history.push(href!.slice(routePrefix.length));
          };
        }
      });
    }

    if (ref.current) {
      drawGraph();
    }
  }, [ref.current, applicationState, shouldIncludeHandles]);
  return (
    <div className={classes.root}>
      <FormGroup row className={classes.formRow}>
        <FormControlLabel
          control={
            <Switch
              checked={shouldIncludeHandles}
              onChange={() =>
                setShouldIncludeHandles(
                  (shouldIncludeHandles) => !shouldIncludeHandles
                )
              }
              name="shouldIncludeHandles"
              color="primary"
            />
          }
          label="Show Handles"
        />
      </FormGroup>
      <div className={classes.graph} ref={ref} />
    </div>
  );
}
