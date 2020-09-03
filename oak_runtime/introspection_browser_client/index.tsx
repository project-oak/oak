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
import ReactDOM from 'react-dom';
import introspectionEventsProto from './proto/introspection_events_pb';

// Requests the list of introspection events provided by the Oak runtime's
// auxiliary introspection server.
function loadSerializedEvents(): Promise<Uint8Array> {
  return new Promise((resolve, reject) => {
    const eventsRequest = new XMLHttpRequest();
    eventsRequest.open(
      'GET',
      // In the development enviroment the introspection client is served by
      // a different server, hence the port of the Oak runtime's auxiliary
      // introspection server must be specified.
      (process.env.NODE_ENV === 'development' ? 'http://localhost:1909' : '') +
        '/introspection-events',
      true
    );
    eventsRequest.responseType = 'arraybuffer';
    eventsRequest.timeout = 10000;

    eventsRequest.addEventListener('load', () =>
      resolve(eventsRequest.response)
    );
    eventsRequest.addEventListener('error', reject);
    eventsRequest.addEventListener('abort', reject);

    eventsRequest.send(null);
  });
}

const EventList = () => {
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

  return (
    <ol>
      {events.map((event, index) => (
        // Usually it's not advisable to use the index as a key. However since
        // the list of events is append-only it's fine in this case.
        // Ref: https://reactjs.org/docs/lists-and-keys.html#keys
        <li key={index}>{JSON.stringify(event.toObject())}</li>
      ))}
    </ol>
  );
};

ReactDOM.render(<EventList />, document.getElementById('app'));
