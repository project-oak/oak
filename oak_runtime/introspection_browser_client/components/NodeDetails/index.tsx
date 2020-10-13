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
import ObjectAsTree from '~/components/ObjectAsTree';
import DetailsDialog, { DetailsDialogProps } from '~/components/DetailsDialog';

type NodeDetailsProps = {
  applicationState: OakApplicationState;
  open: DetailsDialogProps['open'];
  onClose: DetailsDialogProps['onClose'];
};

interface ParamTypes {
  nodeId: string;
}

export default function NodeDetails({
  applicationState,
  open,
  onClose,
}: NodeDetailsProps) {
  const { nodeId } = useParams<ParamTypes>();
  const node = applicationState.nodeInfos.get(nodeId);

  return (
    <DetailsDialog
      onClose={onClose}
      open={open}
      title={`Node Details: ${node?.name ?? `Node ${nodeId}`}`}
      titleId="node-details-dialog-title"
    >
      {node === undefined ? (
        <p>A node with the ID: {nodeId} does not exist.</p>
      ) : (
        <ObjectAsTree data={{ id: nodeId, ...node }} />
      )}
    </DetailsDialog>
  );
}
