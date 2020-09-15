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
const fs = require('fs');
const { promisify } = require('util');
const rimraf = require('rimraf');

const readFileAsync = promisify(fs.readFile);
const writeFileAsync = promisify(fs.writeFile);
const rimrafAsync = promisify(rimraf);

const OUTPUT_DIR = './dist';
const TEMP_OUTPUT_DIR = './dist-tmp';

// Webpack plugin that copies generated assets to a seperate destinationDir.
// If an identical file exists in the destinationDir, it is not overwritten.
// Used to preserve the last `lastModified` metadata of unchanged outputs,
// thereby preventing cargo from rebuilding crates that include them.
// Ref: https://github.com/project-oak/oak/issues/1456
class CopyIfNonExistent {
  constructor(
    options = {
      sourceDir: undefined,
      destinationDir: undefined,
      deleteSourceDir: false,
    }
  ) {
    if ([options.sourceDir, options.destinationDir].includes(undefined)) {
      throw new Error(
        'Both `sourceDir` and `destinationDir` options must be provided'
      );
    }

    this.options = options;
  }
  static areIdenticalFiles(fileA, fileB) {
    if (typeof fileA === 'string' && typeof fileB === 'string') {
      return fileA === fileB;
    }

    if (Buffer.isBuffer(fileA) && Buffer.isBuffer(fileB)) {
      return fileA.equals(fileB);
    }

    return false;
  }
  apply(compiler) {
    compiler.hooks.assetEmitted.tapPromise(
      'CopyIfNonExistent',
      async (fileName, fileContent) => {
        if (!fs.existsSync(this.options.destinationDir)) {
          fs.mkdirSync(this.options.destinationDir);
        }

        const outputPath = `${this.options.destinationDir}/${fileName}`;

        if (!fs.existsSync(outputPath)) {
          return writeFileAsync(outputPath, fileContent);
        }

        const existingFileContent = await readFileAsync(outputPath);

        if (
          CopyIfNonExistent.areIdenticalFiles(fileContent, existingFileContent)
        ) {
          // An identical file already exists, don't overwrite it.
          return;
        }

        return writeFileAsync(outputPath, fileContent);
      }
    );

    compiler.hooks.afterEmit.tapPromise('CopyIfNonExistent', async () => {
      if (this.options.deleteSourceDir) {
        return rimrafAsync(this.options.sourceDir);
      }
    });
  }
}

module.exports = (env) => ({
  entry: './index.tsx',
  output: {
    path: path.resolve(__dirname, TEMP_OUTPUT_DIR),
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
    // Needs to be last in the array, as it moves assets to a seperate dir.
    new CopyIfNonExistent({
      sourceDir: TEMP_OUTPUT_DIR,
      destinationDir: OUTPUT_DIR,
      deleteSourceDir: true,
    }),
  ],
  module: {
    rules: [
      {
        test: /\.tsx?$/,
        use: 'ts-loader',
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
