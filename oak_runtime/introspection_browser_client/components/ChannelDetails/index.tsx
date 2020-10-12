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
import { useParams } from 'react-router-dom';
import ObjectAsTree from '~/components/ObjectAsTree';
import DetailsDialog, { DetailsDialogProps } from '~/components/DetailsDialog';
import { OakApplicationState } from '~/components/Root';

interface ChannelDetailsProps {
  applicationState: OakApplicationState;
  open: DetailsDialogProps['open'];
  onClose: DetailsDialogProps['onClose'];
}

interface ParamTypes {
  channelId: string;
}

export default function ChannelDetails({
  applicationState,
  open,
  onClose,
}: ChannelDetailsProps) {
  const { channelId } = useParams<ParamTypes>();
  const channel = applicationState.channels.get(channelId);

  return (
    <DetailsDialog
      onClose={onClose}
      open={open}
      title={`Channel Details: channel${channelId}`}
      titleId="channel-details-dialog-title"
    >
      {channel === undefined ? (
        <p>A channel with the ID: {channelId} does not exist.</p>
      ) : (
        <ObjectAsTree data={channel} />
      )}
    </DetailsDialog>
  );
}
