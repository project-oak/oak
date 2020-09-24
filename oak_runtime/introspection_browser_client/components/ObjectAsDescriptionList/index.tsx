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

export default function ObjectAsDescriptionList({
  object,
}: {
  object: Object;
}) {
  const classes = useObjectAsDescriptionListStyles();
  return (
    <dl className={classes.dl}>
      {Object.entries(object).map(([key, value]) => (
        <>
          <dt className={classes.dt}>{key}</dt>
          <dd className={classes.dd}>
            {
              // The array check needs to come first, since
              // typeof [1,2,3] === 'object'
              Array.isArray(value) ? (
                JSON.stringify(value)
              ) : // Check for null alongside the object check, since
              // typeof null === 'object'
              typeof value === 'object' && value !== null ? (
                <ObjectAsDescriptionList object={value} />
              ) : (
                value
              )
            }
          </dd>
        </>
      ))}
    </dl>
  );
}
