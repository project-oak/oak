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
import { makeStyles, Theme } from '@material-ui/core/styles';
import DialogTitle from '@material-ui/core/DialogTitle';
import Dialog, { DialogProps } from '@material-ui/core/Dialog';
import DialogContent from '@material-ui/core/DialogContent';
import Button from '@material-ui/core/Button';

const useStyles = makeStyles((theme: Theme) => ({
  closeButton: {
    float: 'right',
    marginLeft: theme.spacing(2),
  },
}));

export interface DetailsDialogProps {
  open: DialogProps['open'];
  onClose: () => void;
  children: React.ReactNode;
  title: string;
  titleId: string;
}

export default function DetailsDialog({
  open,
  onClose,
  children,
  title,
  titleId,
}: DetailsDialogProps) {
  const classes = useStyles();
  return (
    <Dialog
      transitionDuration={0}
      maxWidth={'sm'}
      fullWidth={true}
      onClose={onClose}
      aria-labelledby={titleId}
      open={open}
    >
      <DialogTitle id={titleId}>
        {title}
        <Button className={classes.closeButton} size="small" onClick={onClose}>
          Close
        </Button>
      </DialogTitle>
      <DialogContent>{children}</DialogContent>
    </Dialog>
  );
}
50;
