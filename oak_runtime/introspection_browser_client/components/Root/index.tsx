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
import CssBaseline from '@material-ui/core/CssBaseline';
import Box from '@material-ui/core/Box';
import ApplicationStateOverview from '~/components/ApplicationStateOverview';
import StateGraph from '~/components/StateGraph';
import EventList from '~/components/EventList';
import MainTabs from '~/components/MainTabs';
import introspectionEventsProto, {
  DirectionMap,
} from '~/protoc_out/proto/introspection_events_pb';
import { Label } from '~/protoc_out/oak_abi/proto/label_pb.d';

// Requests the list of introspection events provided by the Oak runtime's
// auxiliary introspection server.
function loadSerializedEvents(): Promise<Uint8Array> {
  return new Promise((resolve, reject) => {
    const eventsRequest = new XMLHttpRequest();
    eventsRequest.open(
      'GET',
      'http://localhost:1909/introspection-events',
      true
    );
    eventsRequest.responseType = 'arraybuffer';

    eventsRequest.addEventListener('load', () =>
      resolve(eventsRequest.response)
    );
    eventsRequest.addEventListener('error', reject);
    eventsRequest.addEventListener('abort', reject);

    eventsRequest.send(null);
  });
}

export interface OakApplicationState {
  nodeInfos: NodeInfos;
  channels: Channels;
}

export type NodeId = bigint;
export type AbiHandle = bigint;
type NodeInfos = Map<NodeId, NodeInfo>;
interface NodeInfo {
  name: string;
  abiHandles: Map<AbiHandle, ChannelHalf>;
  label: Label;
}

export type ChannelID = bigint;
export enum ChannelHalfDirection {
  Read = 'READ',
  Write = 'WRITE',
}
interface ChannelHalf {
  channelId: ChannelID;
  direction: ChannelHalfDirection;
}
interface Message {
  data: Uint8Array;
  channels: ChannelHalf[];
}
interface Channel {
  id: ChannelID;
  messages: Message[];
  label: Label;
}
type Channels = Map<ChannelID, Channel>;

function protoDirectionToChannelHalfDirection(
  direction: DirectionMap[keyof DirectionMap]
): ChannelHalfDirection {
  switch (direction) {
    case introspectionEventsProto.Direction.READ:
      return ChannelHalfDirection.Read;

    case introspectionEventsProto.Direction.WRITE:
      return ChannelHalfDirection.Write;

    default:
      // This should never happen
      throw new Error(`Encountered unhandled direction value ${direction}`);
  }
}

function eventReducer(
  applicationState: OakApplicationState,
  event: introspectionEventsProto.Event
) {
  const eventType = event.getEventDetailsCase();
  const { EventDetailsCase } = introspectionEventsProto.Event;

  switch (eventType) {
    case EventDetailsCase.NODE_CREATED:
      applicationState.nodeInfos.set(
        BigInt(event!.getNodeCreated()!.getNodeId()),
        {
          name: event!.getNodeCreated()!.getName(),
          abiHandles: new Map(),
          label: event!.getNodeCreated()!.getLabel()!,
        }
      );

      break;
    case EventDetailsCase.NODE_DESTROYED:
      {
        const nodeId = BigInt(event!.getNodeDestroyed()!.getNodeId());
        if (applicationState.nodeInfos.delete(nodeId) === false) {
          throw new Error(
            `Couldn't delete Node with id "${nodeId}", as it does not exist.`
          );
        }
      }

      break;
    case EventDetailsCase.CHANNEL_CREATED:
      {
        const channel = event!.getChannelCreated()!;
        const channelId = BigInt(channel.getChannelId());
        applicationState.channels.set(channelId, {
          id: channelId,
          messages: [],
          label: channel.getLabel()!,
        });
      }

      break;
    case EventDetailsCase.CHANNEL_DESTROYED:
      {
        const channelId = BigInt(event!.getChannelDestroyed()!.getChannelId());
        if (applicationState.channels.delete(channelId) === false) {
          throw new Error(
            `Couldn't delete Channel with id "${channelId}", as it does not exist.`
          );
        }
      }

      break;
    case EventDetailsCase.HANDLE_CREATED:
      {
        const details = event.getHandleCreated();
        const nodeId = BigInt(details!.getNodeId());
        const node = applicationState.nodeInfos.get(nodeId);

        if (node === undefined) {
          throw new Error(
            `Couldn't get Node with id "${nodeId}", as it does not exist.`
          );
        }

        const direction = node.abiHandles.set(BigInt(details!.getHandle()), {
          channelId: BigInt(details!.getChannelId()),
          direction: protoDirectionToChannelHalfDirection(
            details!.getDirection()
          ),
        });
      }

      break;
    case EventDetailsCase.HANDLE_DESTROYED:
      {
        const details = event.getHandleDestroyed();
        const nodeId = BigInt(details!.getNodeId());
        const node = applicationState.nodeInfos.get(nodeId);

        if (node === undefined) {
          throw new Error(
            `Couldn't get Node with id "${nodeId}", as it does not exist.`
          );
        }

        const handle = BigInt(details!.getHandle());

        if (node.abiHandles.delete(handle) === false) {
          throw new Error(
            `Couldn't delete ABI handle "${handle}" on Node with id "${nodeId}", as it does not exist.`
          );
        }
      }

      break;
    case EventDetailsCase.MESSAGE_ENQUEUED:
      // TODO(#913): Add support for displaying messages

      break;
    case EventDetailsCase.MESSAGE_DEQUEUED:
      // TODO(#913): Add support for displaying messages

      break;
    default:
      // This should never happen
      throw new Error(`Encountered unhandled event of type ${eventType}`);
  }

  return applicationState;
}

function useEvents() {
  const [events, setEvents] = React.useState<introspectionEventsProto.Event[]>(
    []
  );
  React.useEffect(() => {
    async function loadEvents() {
      const serializedEvents: Uint8Array = await loadSerializedEvents();
      const events = introspectionEventsProto.Events.deserializeBinary(
        serializedEvents
      ).getEventsList();
      setEvents(events);
    }

    loadEvents();
  }, []);

  return events;
}

export default function Root() {
  const events = useEvents();
  const applicationState = React.useMemo(
    (): OakApplicationState =>
      events.reduce(eventReducer, {
        nodeInfos: new Map(),
        channels: new Map(),
      }),
    [events]
  );

  return (
    <>
      <CssBaseline />
      <MainTabs
        tabs={[
          {
            label: 'Application Graph',
            render: () => <StateGraph applicationState={applicationState} />,
          },
          {
            label: 'Application State',
            render: () => (
              <Box p={3}>
                <ApplicationStateOverview applicationState={applicationState} />
              </Box>
            ),
          },
          {
            label: 'Event List',
            render: () => (
              <Box p={3}>
                <EventList events={events} />
              </Box>
            ),
          },
        ]}
      />
    </>
  );
}
