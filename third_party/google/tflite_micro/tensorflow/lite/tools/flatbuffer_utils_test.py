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
"""Tests for flatbuffer_utils.py."""
import copy
import os
import subprocess

from tflite_micro.tensorflow.lite.tools import flatbuffer_utils
from tflite_micro.tensorflow.lite.tools import test_utils
from tensorflow.python.framework import test_util
from tensorflow.python.platform import test

_SKIPPED_BUFFER_INDEX = 1


class WriteReadModelTest(test_util.TensorFlowTestCase):

  def testWriteReadModel(self):
    # 1. SETUP
    # Define the initial model
    initial_model = test_utils.build_mock_model()
    # Define temporary files
    tmp_dir = self.get_temp_dir()
    model_filename = os.path.join(tmp_dir, 'model.tflite')

    # 2. INVOKE
    # Invoke the write_model and read_model functions
    flatbuffer_utils.write_model(initial_model, model_filename)
    final_model = flatbuffer_utils.read_model(model_filename)

    # 3. VALIDATE
    # Validate that the initial and final models are the same
    # Validate the description
    self.assertEqual(initial_model.description, final_model.description)
    # Validate the main subgraph's name, inputs, outputs, operators and tensors
    initial_subgraph = initial_model.subgraphs[0]
    final_subgraph = final_model.subgraphs[0]
    self.assertEqual(initial_subgraph.name, final_subgraph.name)
    for i in range(len(initial_subgraph.inputs)):
      self.assertEqual(initial_subgraph.inputs[i], final_subgraph.inputs[i])
    for i in range(len(initial_subgraph.outputs)):
      self.assertEqual(initial_subgraph.outputs[i], final_subgraph.outputs[i])
    for i in range(len(initial_subgraph.operators)):
      self.assertEqual(initial_subgraph.operators[i].opcodeIndex,
                       final_subgraph.operators[i].opcodeIndex)
    initial_tensors = initial_subgraph.tensors
    final_tensors = final_subgraph.tensors
    for i in range(len(initial_tensors)):
      self.assertEqual(initial_tensors[i].name, final_tensors[i].name)
      self.assertEqual(initial_tensors[i].type, final_tensors[i].type)
      self.assertEqual(initial_tensors[i].buffer, final_tensors[i].buffer)
      for j in range(len(initial_tensors[i].shape)):
        self.assertEqual(initial_tensors[i].shape[j], final_tensors[i].shape[j])
    # Validate the first valid buffer (index 0 is always None)
    initial_buffer = initial_model.buffers[1].data
    final_buffer = final_model.buffers[1].data
    for i in range(initial_buffer.size):
      self.assertEqual(initial_buffer.data[i], final_buffer.data[i])


class StripStringsTest(test_util.TensorFlowTestCase):

  def testStripStrings(self):
    # 1. SETUP
    # Define the initial model
    initial_model = test_utils.build_mock_model()
    final_model = copy.deepcopy(initial_model)

    # 2. INVOKE
    # Invoke the strip_strings function
    flatbuffer_utils.strip_strings(final_model)

    # 3. VALIDATE
    # Validate that the initial and final models are the same except strings
    # Validate the description
    self.assertIsNotNone(initial_model.description)
    self.assertIsNone(final_model.description)
    self.assertIsNotNone(initial_model.signatureDefs)
    self.assertIsNone(final_model.signatureDefs)

    # Validate the main subgraph's name, inputs, outputs, operators and tensors
    initial_subgraph = initial_model.subgraphs[0]
    final_subgraph = final_model.subgraphs[0]
    self.assertIsNotNone(initial_model.subgraphs[0].name)
    self.assertIsNone(final_model.subgraphs[0].name)
    for i in range(len(initial_subgraph.inputs)):
      self.assertEqual(initial_subgraph.inputs[i], final_subgraph.inputs[i])
    for i in range(len(initial_subgraph.outputs)):
      self.assertEqual(initial_subgraph.outputs[i], final_subgraph.outputs[i])
    for i in range(len(initial_subgraph.operators)):
      self.assertEqual(initial_subgraph.operators[i].opcodeIndex,
                       final_subgraph.operators[i].opcodeIndex)
    initial_tensors = initial_subgraph.tensors
    final_tensors = final_subgraph.tensors
    for i in range(len(initial_tensors)):
      self.assertIsNotNone(initial_tensors[i].name)
      self.assertIsNone(final_tensors[i].name)
      self.assertEqual(initial_tensors[i].type, final_tensors[i].type)
      self.assertEqual(initial_tensors[i].buffer, final_tensors[i].buffer)
      for j in range(len(initial_tensors[i].shape)):
        self.assertEqual(initial_tensors[i].shape[j], final_tensors[i].shape[j])
    # Validate the first valid buffer (index 0 is always None)
    initial_buffer = initial_model.buffers[1].data
    final_buffer = final_model.buffers[1].data
    for i in range(initial_buffer.size):
      self.assertEqual(initial_buffer.data[i], final_buffer.data[i])


class RandomizeWeightsTest(test_util.TensorFlowTestCase):

  def testRandomizeWeights(self):
    # 1. SETUP
    # Define the initial model
    initial_model = test_utils.build_mock_model()
    final_model = copy.deepcopy(initial_model)

    # 2. INVOKE
    # Invoke the randomize_weights function
    flatbuffer_utils.randomize_weights(final_model)

    # 3. VALIDATE
    # Validate that the initial and final models are the same, except that
    # the weights in the model buffer have been modified (i.e, randomized)
    # Validate the description
    self.assertEqual(initial_model.description, final_model.description)
    # Validate the main subgraph's name, inputs, outputs, operators and tensors
    initial_subgraph = initial_model.subgraphs[0]
    final_subgraph = final_model.subgraphs[0]
    self.assertEqual(initial_subgraph.name, final_subgraph.name)
    for i in range(len(initial_subgraph.inputs)):
      self.assertEqual(initial_subgraph.inputs[i], final_subgraph.inputs[i])
    for i in range(len(initial_subgraph.outputs)):
      self.assertEqual(initial_subgraph.outputs[i], final_subgraph.outputs[i])
    for i in range(len(initial_subgraph.operators)):
      self.assertEqual(initial_subgraph.operators[i].opcodeIndex,
                       final_subgraph.operators[i].opcodeIndex)
    initial_tensors = initial_subgraph.tensors
    final_tensors = final_subgraph.tensors
    for i in range(len(initial_tensors)):
      self.assertEqual(initial_tensors[i].name, final_tensors[i].name)
      self.assertEqual(initial_tensors[i].type, final_tensors[i].type)
      self.assertEqual(initial_tensors[i].buffer, final_tensors[i].buffer)
      for j in range(len(initial_tensors[i].shape)):
        self.assertEqual(initial_tensors[i].shape[j], final_tensors[i].shape[j])
    # Validate the first valid buffer (index 0 is always None)
    initial_buffer = initial_model.buffers[1].data
    final_buffer = final_model.buffers[1].data
    for j in range(initial_buffer.size):
      self.assertNotEqual(initial_buffer.data[j], final_buffer.data[j])

  def testRandomizeSomeWeights(self):
    # 1. SETUP
    # Define the initial model
    initial_model = test_utils.build_mock_model()
    final_model = copy.deepcopy(initial_model)

    # 2. INVOKE
    # Invoke the randomize_weights function, but skip the first buffer
    flatbuffer_utils.randomize_weights(
        final_model, buffers_to_skip=[_SKIPPED_BUFFER_INDEX])

    # 3. VALIDATE
    # Validate that the initial and final models are the same, except that
    # the weights in the model buffer have been modified (i.e, randomized)
    # Validate the description
    self.assertEqual(initial_model.description, final_model.description)
    # Validate the main subgraph's name, inputs, outputs, operators and tensors
    initial_subgraph = initial_model.subgraphs[0]
    final_subgraph = final_model.subgraphs[0]
    self.assertEqual(initial_subgraph.name, final_subgraph.name)
    for i, _ in enumerate(initial_subgraph.inputs):
      self.assertEqual(initial_subgraph.inputs[i], final_subgraph.inputs[i])
    for i, _ in enumerate(initial_subgraph.outputs):
      self.assertEqual(initial_subgraph.outputs[i], final_subgraph.outputs[i])
    for i, _ in enumerate(initial_subgraph.operators):
      self.assertEqual(initial_subgraph.operators[i].opcodeIndex,
                       final_subgraph.operators[i].opcodeIndex)
    initial_tensors = initial_subgraph.tensors
    final_tensors = final_subgraph.tensors
    for i, _ in enumerate(initial_tensors):
      self.assertEqual(initial_tensors[i].name, final_tensors[i].name)
      self.assertEqual(initial_tensors[i].type, final_tensors[i].type)
      self.assertEqual(initial_tensors[i].buffer, final_tensors[i].buffer)
      for j in range(len(initial_tensors[i].shape)):
        self.assertEqual(initial_tensors[i].shape[j], final_tensors[i].shape[j])
    # Validate that the skipped buffer is unchanged.
    initial_buffer = initial_model.buffers[_SKIPPED_BUFFER_INDEX].data
    final_buffer = final_model.buffers[_SKIPPED_BUFFER_INDEX].data
    for j in range(initial_buffer.size):
      self.assertEqual(initial_buffer.data[j], final_buffer.data[j])


class XxdOutputToBytesTest(test_util.TensorFlowTestCase):

  def testXxdOutputToBytes(self):
    # 1. SETUP
    # Define the initial model
    initial_model = test_utils.build_mock_model()
    initial_bytes = flatbuffer_utils.convert_object_to_bytearray(initial_model)

    # Define temporary files
    tmp_dir = self.get_temp_dir()
    model_filename = os.path.join(tmp_dir, 'model.tflite')

    # 2. Write model to temporary file (will be used as input for xxd)
    flatbuffer_utils.write_model(initial_model, model_filename)

    # 3. DUMP WITH xxd
    input_cc_file = os.path.join(tmp_dir, 'model.cc')

    command = 'xxd -i {} > {}'.format(model_filename, input_cc_file)
    subprocess.call(command, shell=True)

    # 4. VALIDATE
    final_bytes = flatbuffer_utils.xxd_output_to_bytes(input_cc_file)

    # Validate that the initial and final bytearray are the same
    self.assertEqual(initial_bytes, final_bytes)


if __name__ == '__main__':
  test.main()
