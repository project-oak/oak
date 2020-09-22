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

type NodeDetailsProps = {
  applicationState: OakApplicationState;
};

interface ParamTypes {
  nodeId: string;
}

export default function NodeDetails({ applicationState }: NodeDetailsProps) {
  const { nodeId } = useParams<ParamTypes>();
  const node = applicationState.nodeInfos.get(BigInt(nodeId));

  if (node === undefined) {
    return <p>A node with the ID: {nodeId} does not exist.</p>;
  }

  return <div>{JSON.stringify(node)}</div>;
}
