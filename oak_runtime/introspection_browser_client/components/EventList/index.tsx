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
import introspectionEventsProto from '~/protoc_out/introspection_events_pb';

type EventListProps = { events: introspectionEventsProto.Event[] };

export default function EventList({ events }: EventListProps) {
  return (
    <section>
      <strong>Events List</strong>
      <ol>
        {events.map((event, index) => (
          // Usually it's not advisable to use the index as a key. However since
          // the list of events is append-only it's fine in this case.
          // Ref: https://reactjs.org/docs/lists-and-keys.html#keys
          <li key={index}>{JSON.stringify(event.toObject())}</li>
        ))}
      </ol>
    </section>
  );
}
