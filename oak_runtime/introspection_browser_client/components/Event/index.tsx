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
import { makeStyles } from '@material-ui/core/styles';
import { useParams } from 'react-router-dom';
import ObjectAsTree from '~/components/ObjectAsTree';
import DetailsDialog, { DetailsDialogProps } from '~/components/DetailsDialog';
import { NodeId } from '~/components/Root';
import ObjectAsDescriptionList, {
  InlineDl,
  InlineDt,
  InlineDd,
} from '~/components/ObjectAsDescriptionList';
import introspectionEventsProto from '~/protoc_out/proto/introspection_events_pb';

function camelCaseToTitleCase(camelCase: string) {
  return camelCase
    .replace(/([A-Z])/g, (match) => ` ${match}`)
    .replace(/^./, (match) => match.toUpperCase());
}

function getEventDetails(event: introspectionEventsProto.Event) {
  const { timestamp, ...rest } = event.toObject();

  // The event details will have entries for each possible type defined the
  // protobuf enum. The one whose value is not undefined represents the details
  // of this object.
  return Object.entries(rest).find(
    ([eventType, eventDetails]) => eventDetails !== undefined
  )!;
}

interface EventDetailsDialogProps {
  totalEvents: introspectionEventsProto.Event[];
  open: DetailsDialogProps['open'];
  onClose: DetailsDialogProps['onClose'];
}

interface ParamTypes {
  eventIndex: string;
}

export function EventDetailsDialog({
  totalEvents,
  open,
  onClose,
}: EventDetailsDialogProps) {
  const { eventIndex: eventIndexParam } = useParams<ParamTypes>();
  const eventIndex = parseInt(eventIndexParam);
  const event = totalEvents[eventIndex];

  if (event === undefined) {
    return (
      <DetailsDialog
        onClose={onClose}
        open={open}
        title={'Not found'}
        titleId="change-details-dialog-title"
      >
        <p>A change with the index: {eventIndex} does not exist.</p>
      </DetailsDialog>
    );
  }

  const [eventType, eventDetails] = getEventDetails(event);

  return (
    <DetailsDialog
      onClose={onClose}
      open={open}
      title={`Change Details: ${camelCaseToTitleCase(eventType)}`}
      titleId="change-details-dialog-title"
    >
      <strong>Change Metadata:</strong>
      <ObjectAsTree
        data={{
          changeIndex: eventIndex,
          changeTime: event.getTimestamp()!.toDate().toISOString(),
          changeType: camelCaseToTitleCase(eventType),
        }}
      />
      <br />
      <strong>Change Data:</strong>
      <ObjectAsTree data={eventDetails} />
    </DetailsDialog>
  );
}

function renderEventDescription(
  event: introspectionEventsProto.Event,
  nodeIdsToNodeNames: Map<NodeId, string>
): { description: React.ReactNode; title: string } {
  const { EventDetailsCase } = introspectionEventsProto.Event;

  if (event.getEventDetailsCase() === EventDetailsCase.NODE_CREATED) {
    return {
      title: `Node Created`,
      description: (
        <ObjectAsDescriptionList
          object={{
            name: event.getNodeCreated()!.getName(),
            id: event.getNodeCreated()!.getNodeId(),
            label: event.getNodeCreated()!.getLabel()!.toObject(),
          }}
          dlComponent={InlineDl}
          dtComponent={InlineDt}
          ddComponent={InlineDd}
        />
      ),
    };
  }

  if (event.getEventDetailsCase() === EventDetailsCase.NODE_DESTROYED) {
    return {
      title: `Node Destroyed`,
      description: (
        <ObjectAsDescriptionList
          object={{
            name: nodeIdsToNodeNames.get(event.getNodeDestroyed()!.getNodeId()),
            id: event.getNodeDestroyed()!.getNodeId(),
          }}
          dlComponent={InlineDl}
          dtComponent={InlineDt}
          ddComponent={InlineDd}
        />
      ),
    };
  }

  if (event.getEventDetailsCase() === EventDetailsCase.CHANNEL_CREATED) {
    return {
      title: `Channel Created`,
      description: (
        <ObjectAsDescriptionList
          object={{
            id: event.getChannelCreated()!.getChannelId(),
            name: event.getChannelCreated()!.getName(),
            label: event.getChannelCreated()!.getLabel()!.toObject(),
          }}
          dlComponent={InlineDl}
          dtComponent={InlineDt}
          ddComponent={InlineDd}
        />
      ),
    };
  }

  if (event.getEventDetailsCase() === EventDetailsCase.CHANNEL_DESTROYED) {
    return {
      title: `Channel Destroyed`,
      description: (
        <ObjectAsDescriptionList
          object={{
            id: event.getChannelDestroyed()!.getChannelId(),
          }}
          dlComponent={InlineDl}
          dtComponent={InlineDt}
          ddComponent={InlineDd}
        />
      ),
    };
  }

  if (event.getEventDetailsCase() === EventDetailsCase.HANDLE_CREATED) {
    return event.getHandleCreated()!.getDirection() ===
      introspectionEventsProto.Direction.READ
      ? {
          title: 'Handle Created',
          description: `${nodeIdsToNodeNames.get(
            event.getHandleCreated()!.getNodeId()
          )} read from channel${event
            .getHandleCreated()!
            .getChannelId()} (${event.getHandleCreated()!.getHandle()})`,
        }
      : {
          title: 'Handle Created',
          description: `${nodeIdsToNodeNames.get(
            event.getHandleCreated()!.getNodeId()
          )} write to channel${event
            .getHandleCreated()!
            .getChannelId()} (${event.getHandleCreated()!.getHandle()})`,
        };
  }

  if (event.getEventDetailsCase() === EventDetailsCase.HANDLE_DESTROYED) {
    return event.getHandleDestroyed()!.getDirection() ===
      introspectionEventsProto.Direction.READ
      ? {
          title: 'Handle Destroyed',
          description: `${nodeIdsToNodeNames.get(
            event.getHandleDestroyed()!.getNodeId()
          )} read from channel${event
            .getHandleDestroyed()!
            .getChannelId()} (${event.getHandleDestroyed()!.getHandle()})`,
        }
      : {
          title: 'Handle Destroyed',
          description: `${nodeIdsToNodeNames.get(
            event.getHandleDestroyed()!.getNodeId()
          )} write to channel${event
            .getHandleDestroyed()!
            .getChannelId()} (${event.getHandleDestroyed()!.getHandle()})`,
        };
  }

  if (event.getEventDetailsCase() === EventDetailsCase.MESSAGE_ENQUEUED) {
    return {
      title: `Message Enqueued`,
      description: (
        <>
          {nodeIdsToNodeNames.get(event.getMessageEnqueued()!.getNodeId())} to
          channel
          {event.getMessageEnqueued()!.getChannelId()},{' '}
          <ObjectAsDescriptionList
            object={{
              includedHandles: event
                .getMessageEnqueued()!
                .getIncludedHandlesList(),
            }}
            dlComponent={InlineDl}
            dtComponent={InlineDt}
            ddComponent={InlineDd}
          />
        </>
      ),
    };
  }

  if (event.getEventDetailsCase() === EventDetailsCase.MESSAGE_DEQUEUED) {
    return {
      title: `Message Dequeued`,
      description: (
        <>
          channel{event.getMessageDequeued()!.getChannelId()} to{' '}
          {nodeIdsToNodeNames.get(event.getMessageDequeued()!.getNodeId())},{' '}
          <ObjectAsDescriptionList
            object={{
              includedHandles: event
                .getMessageDequeued()!
                .getAcquiredHandlesList(),
            }}
            dlComponent={InlineDl}
            dtComponent={InlineDt}
            ddComponent={InlineDd}
          />
        </>
      ),
    };
  }

  const [eventType, eventDetails] = getEventDetails(event);
  return {
    title: camelCaseToTitleCase(eventType),
    description: (
      <ObjectAsDescriptionList
        object={eventDetails}
        dlComponent={InlineDl}
        dtComponent={InlineDt}
        ddComponent={InlineDd}
      />
    ),
  };
}

const useStyles = makeStyles({
  descriptionWrapper: {
    overflow: 'hidden',
    textOverflow: 'ellipsis',
  },
});

export default function Event({
  event,
  nodeIdsToNodeNames,
}: {
  event: introspectionEventsProto.Event;
  nodeIdsToNodeNames: Map<NodeId, string>;
}) {
  const eventTime = event.getTimestamp()!.toDate();
  const { title, description } = renderEventDescription(
    event,
    nodeIdsToNodeNames
  );

  const classes = useStyles();

  return (
    <div>
      <div>
        <strong>{title}</strong>
        <span>
          {' '}
          at{' '}
          <time dateTime={eventTime.toISOString()}>
            {eventTime.getUTCHours()}:{eventTime.getUTCMinutes()}:
            {eventTime.getUTCSeconds()} UTC
          </time>
        </span>
      </div>
      <div className={classes.descriptionWrapper}>{description}</div>
    </div>
  );
}
