import React from 'react';
import JSONTree from 'react-json-tree';

// Taken from https://github.com/Alchiadus/base16-syntax/blob/master/styles/schemes/github.less
const THEME = {
  base00: '#ffffff',
  base01: '#f5f5f5',
  base02: '#c8c8fa',
  base03: '#969896',
  base04: '#e8e8e8',
  base05: '#333333',
  base06: '#ffffff',
  base07: '#ffffff',
  base08: '#ed6a43',
  base09: '#0086b3',
  base0A: '#795da3',
  base0B: '#183691',
  base0C: '#183691',
  base0D: '#795da3',
  base0E: '#a71d5d',
  base0F: '#333333',
};

export default function ObjectAsTree({ data }: { data: any }) {
  return <JSONTree theme={THEME} invertTheme={false} hideRoot data={data} />;
}
