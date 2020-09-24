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
import { OakApplicationState } from '~/components/Root';

type HandleDetailsProps = {
  applicationState: OakApplicationState;
};

interface ParamTypes {
  nodeId: string;
  handle: string;
}

export default function HandleDetails({
  applicationState,
}: HandleDetailsProps) {
  const { nodeId, handle } = useParams<ParamTypes>();
  const node = applicationState.nodeInfos.get(BigInt(nodeId));

  if (node === undefined) {
    return <p>A node with the ID: {node} does not exist.</p>;
  }

  const channelHalf = node.abiHandles.get(BigInt(handle));

  if (channelHalf === undefined) {
    return (
      <p>
        The handle {handle} does not exist on the node with the ID: {node}.
      </p>
    );
  }

  return (
    <p>
      The handle {handle} of the node {nodeId} maps to channel{' '}
      {channelHalf.channelId.toString()} {channelHalf.direction}
    </p>
  );
}
