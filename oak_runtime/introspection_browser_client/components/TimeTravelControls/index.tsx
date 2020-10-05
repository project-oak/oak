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

const useStyles = makeStyles(() => ({
  wrapper: {
    display: 'flex',
    padding: '5px',
  },

  backWrapper: {
    margin: '5px',
  },

  forthWrapper: { margin: '5px' },
}));

type EventListProps = { back: () => JSX.Element; forth: () => JSX.Element };

export default function EventList({ back, forth }: EventListProps) {
  const classes = useStyles();
  return (
    <div className={classes.wrapper}>
      <div className={classes.backWrapper}>{back()}</div>
      <div className={classes.forthWrapper}>{forth()}</div>
    </div>
  );
}
