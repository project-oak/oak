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
import ObjectAsDescriptionList from '~/components/ObjectAsDescriptionList';
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

const useStyles = makeStyles({
  wrapper: { marginBottom: '0.5rem' },
});

export default function Event({
  event,
}: {
  event: introspectionEventsProto.Event;
}) {
  const classes = useStyles();

  const eventTime: string = event.getTimestamp().toDate().toISOString();
  const [eventType, eventDetails] = getEventDetails(event);

  return (
    <div className={classes.wrapper}>
      <div>
        <strong>{camelCaseToTitleCase(eventType)}</strong>
        <span>
          {' '}
          at <time dateTime={eventTime}>{eventTime}</time>
        </span>
      </div>
      <ObjectAsDescriptionList object={eventDetails} />
    </div>
  );
}
