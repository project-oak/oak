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
import { makeStyles } from '@material-ui/core/styles';
import List from '@material-ui/core/List';
import ListItem from '@material-ui/core/ListItem';
import ListItemIcon from '@material-ui/core/ListItemIcon';
import ListItemText from '@material-ui/core/ListItemText';
import ListSubheader from '@material-ui/core/ListSubheader';
import Divider from '@material-ui/core/Divider';
import IconButton from '@material-ui/core/IconButton';
import MoreVertIcon from '@material-ui/icons/MoreVert';
import { NodeId } from '~/components/Root';
import Event from '~/components/Event';
import introspectionEventsProto from '~/protoc_out/proto/introspection_events_pb';

const useStyles = makeStyles({
  list: {
    position: 'relative',
    backgroundColor: 'inherit',
    flexGrow: 1,
  },
  futureEvents: {
    backgroundColor: 'rgb(255 246 233)',
  },
  events: {
    backgroundColor: 'inherit',
  },
  ol: {
    backgroundColor: 'inherit',
    padding: 0,
  },
  listItemWrapper: {
    display: 'flex',
    alignItems: 'center',
    justifyContent: 'space-between',
    paddingRight: '10px',
  },
  listIcon: {
    minWidth: 'unset',
    marginRight: '10px',
  },
  listItem: {
    overflow: 'hidden',
    whiteSpace: 'nowrap',
    textOverflow: 'ellipsis',
  },
  outerChildrenWrapper: {
    position: 'sticky',
    left: 0,
    right: 0,
    bottom: 0,
    backgroundColor: 'inherit',
    zIndex: 2,
  },
  innerChildrenWrapper: {
    padding: '3px 7px',
  },
});

type EventListProps = {
  totalEvents: introspectionEventsProto.Event[];
  presentEventIndex: number;
  className: string;
  setPresentEventIndex: React.Dispatch<React.SetStateAction<number>>;
  children: React.ReactNode;
};

// Array of events in reverse chronological order
type ReversedEvent = {
  // The event index, in the order of event creation
  eventIndex: number;
  // The actual event
  event: introspectionEventsProto.Event;
};

type ReversedEvents = ReversedEvent[];

export default function EventList({
  presentEventIndex,
  totalEvents,
  className,
  setPresentEventIndex,
  children,
}: EventListProps) {
  const classes = useStyles();
  const history = useHistory();
  // Reverse the array of events (while storing the orginal index) to render
  // events in a reverse chronological order.
  const reversedEvents = totalEvents.reduce((acc, event, eventIndex) => {
    acc.unshift({ eventIndex, event });
    return acc;
  }, [] as ReversedEvents);

  const futureEvents = reversedEvents.slice(
    0,
    totalEvents.length - presentEventIndex - 1
  );
  const pastEvents = reversedEvents.slice(
    totalEvents.length - presentEventIndex - 1
  );

  // Assemble a map of nodeIds to names, which allows for rendering event
  // details in a more intuitive manner.
  const nodeIdsToNodeNames = totalEvents.reduce((acc, event, eventIndex) => {
    if (
      event.getEventDetailsCase() ===
      introspectionEventsProto.Event.EventDetailsCase.NODE_CREATED
    ) {
      const details = event.getNodeCreated()!;
      const nodeId = details.getNodeId();
      const name = details.getName();

      acc.set(nodeId, name);
    }

    return acc;
  }, new Map() as Map<NodeId, string>);

  function renderEvent({ eventIndex, event }: ReversedEvent) {
    return (
      // Usually it's not advisable to use the index as a key. However since
      // the list of events is append-only it's fine in this case.
      // Ref: https://reactjs.org/docs/lists-and-keys.html#keys
      <div className={classes.listItemWrapper}>
        <ListItem
          component="li"
          key={eventIndex}
          button
          onClick={() => setPresentEventIndex(eventIndex)}
          dense
          className={classes.listItem}
        >
          <ListItemIcon
            aria-hidden
            classes={{
              root: classes.listIcon,
            }}
          >
            {eventIndex}.
          </ListItemIcon>
          <ListItemText>
            <Event event={event} nodeIdsToNodeNames={nodeIdsToNodeNames} />
          </ListItemText>
        </ListItem>
        <IconButton
          onClick={() => history.push(`/change/${eventIndex}`)}
          aria-label="View change details"
        >
          <MoreVertIcon />
        </IconButton>
      </div>
    );
  }

  return (
    <div className={className}>
      <List
        className={classes.list}
        component="ol"
        aria-label="State change events"
        subheader={<li />}
      >
        <li className={classes.futureEvents}>
          <ol className={classes.ol}>
            <ListSubheader>Future Changes: {futureEvents.length}</ListSubheader>
            {futureEvents.map(renderEvent)}
          </ol>
        </li>
        <Divider />
        <li className={classes.events}>
          <ol className={classes.ol}>
            <ListSubheader>Previous Changes: {pastEvents.length}</ListSubheader>
            {pastEvents.map(renderEvent)}
          </ol>
        </li>
      </List>
      <div className={classes.outerChildrenWrapper}>
        <Divider />
        <div className={classes.innerChildrenWrapper}>{children}</div>
      </div>
    </div>
  );
}
