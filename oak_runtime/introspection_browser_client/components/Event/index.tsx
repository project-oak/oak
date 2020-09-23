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
import introspectionEventsProto from '~/protoc_out/proto/introspection_events_pb';

const useObjectAsDescriptionListStyles = makeStyles({
  dl: {
    display: 'inline',
    '& dl': { '&:before': { content: '"{ "' }, '&:after': { content: '" }"' } },
  },
  dt: {
    display: 'inline',
    margin: 0,
    '&:after': { content: '": "' },
  },
  dd: {
    display: 'inline',
    margin: 0,
    '&:after': { content: '", "' },
    '&:last-of-type': { '&:after': { content: '""' } },
  },
});

function ObjectAsDescriptionList({ object }: { object: Object }) {
  const classes = useObjectAsDescriptionListStyles();
  return (
    <dl className={classes.dl}>
      {Object.entries(object).map(([key, value]) => (
        <>
          <dt className={classes.dt}>{key}</dt>
          <dd className={classes.dd}>
            {Array.isArray(value) ? (
              JSON.stringify(value)
            ) : typeof value === 'object' ? (
              <ObjectAsDescriptionList object={value} />
            ) : (
              value
            )}
          </dd>
        </>
      ))}
    </dl>
  );
}

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
  const [eventType, eventDetails] = Object.entries(rest).find(
    ([key, value]) => value !== undefined
  )!;

  return [eventType, eventDetails];
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

  const eventTime = event.getTimestamp().toDate();
  const [eventType, eventDetails] = getEventDetails(event);

  return (
    <div className={classes.wrapper}>
      <div>
        <strong>{camelCaseToTitleCase(eventType)}</strong>
        <span>
          {' '}
          at{' '}
          <time>
            {eventTime.getUTCHours()}h:{eventTime.getUTCMinutes()}m:
            {eventTime.getUTCSeconds()}.{eventTime.getUTCMilliseconds()}s (UTC)
          </time>
        </span>
      </div>
      <ObjectAsDescriptionList object={eventDetails} />
    </div>
  );
}
