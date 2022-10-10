# Copyright 2020 The TensorFlow Authors. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# ==============================================================================
r"""Randomize all weights in a tflite file."""

from absl import app
from absl import flags

from tflite_micro.tensorflow.lite.tools import flatbuffer_utils

FLAGS = flags.FLAGS

flags.DEFINE_string('input_tflite_file', None,
                    'Full path name to the input TFLite file.')
flags.DEFINE_string('output_tflite_file', None,
                    'Full path name to the output randomized TFLite file.')
flags.DEFINE_multi_integer(
    'buffers_to_skip', [], 'Buffer indices in the TFLite model to be skipped, '
    'i.e., to be left unmodified.')
flags.DEFINE_integer('random_seed', 0, 'Input to the random number generator.')

flags.mark_flag_as_required('input_tflite_file')
flags.mark_flag_as_required('output_tflite_file')


def main(_):
  model = flatbuffer_utils.read_model(FLAGS.input_tflite_file)
  flatbuffer_utils.randomize_weights(model, FLAGS.random_seed,
                                     FLAGS.buffers_to_skip)
  flatbuffer_utils.write_model(model, FLAGS.output_tflite_file)


if __name__ == '__main__':
  app.run(main)
