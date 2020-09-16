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

const path = require('path');
const CopyPlugin = require('copy-webpack-plugin');
const CompressionPlugin = require('compression-webpack-plugin');

module.exports = (env) => ({
  entry: './index.tsx',
  output: {
    path: path.resolve(__dirname, env.OUTPUT_PATH || './dist'),
    filename: 'index.js',
  },
  plugins: [
    new CopyPlugin({
      patterns: [
        { from: './static', to: './' },
        {
          from: './node_modules/@hpcc-js/wasm/dist/graphvizlib.wasm',
          to: './',
        },
      ],
    }),
    ...(env.NODE_ENV === 'production'
      ? [new CompressionPlugin({ deleteOriginalAssets: true })]
      : []),
  ],
  module: {
    rules: [
      {
        test: /\.tsx?$/,
        use: ['cache-loader', 'ts-loader'],
        exclude: /node_modules/,
      },
    ],
  },
  resolve: {
    extensions: ['.ts', '.tsx', '.js'],
    alias: {
      '~': path.resolve(__dirname),
    },
  },
  mode: env.NODE_ENV || 'none',
  devServer: {
    inline: true,
    liveReload: false,
  },
});
