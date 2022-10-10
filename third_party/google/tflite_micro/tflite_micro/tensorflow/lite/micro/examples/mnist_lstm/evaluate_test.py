# Copyright 2022 The TensorFlow Authors. All Rights Reserved.
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
# =============================================================================
import os

import numpy as np
import tensorflow as tf

from tensorflow.python.framework import test_util
from tensorflow.python.platform import resource_loader
from tensorflow.python.platform import test
from tflite_micro.tensorflow.lite.micro.python.interpreter.src import tflm_runtime
from tflite_micro.tensorflow.lite.micro.examples.mnist_lstm import evaluate

PREFIX_PATH = resource_loader.get_path_to_datafile("")


class LSTMModelTest(test_util.TensorFlowTestCase):

  model_path = os.path.join(PREFIX_PATH, "trained_lstm.tflite")
  input_shape = (1, 28, 28)
  output_shape = (1, 10)

  tflm_interpreter = tflm_runtime.Interpreter.from_file(model_path)

  def testCompareWithTFLite(self):
    tflite_interpreter = tf.lite.Interpreter(model_path=self.model_path)
    tflite_interpreter.allocate_tensors()
    tflite_output_details = tflite_interpreter.get_output_details()[0]
    tflite_input_details = tflite_interpreter.get_input_details()[0]

    np.random.seed(42)  #Seed the random number generator
    num_steps = 100
    for _ in range(0, num_steps):
      # Clear the internal states of the TfLite and TFLM interpreters so that we can call invoke multiple times (LSTM is stateful).
      tflite_interpreter.reset_all_variables()
      self.tflm_interpreter.reset()

      # Give the same (random) input to both interpreters can confirm that the output is identical.
      data_x = np.random.random(self.input_shape)
      data_x = data_x.astype("float32")

      # Run inference on TFLite
      tflite_interpreter.set_tensor(tflite_input_details["index"], data_x)
      tflite_interpreter.invoke()
      tflite_output = tflite_interpreter.get_tensor(
          tflite_output_details["index"])

      # Run inference on TFLM
      self.tflm_interpreter.set_input(data_x, 0)
      self.tflm_interpreter.invoke()
      tflm_output = self.tflm_interpreter.get_output(0)

      # Check that TFLM has correct output
      self.assertDTypeEqual(tflm_output, np.float32)
      self.assertEqual(tflm_output.shape, self.output_shape)
      self.assertAllLess((tflite_output - tflm_output), 1e-5)

  def testInputErrHandling(self):
    wrong_size_image_path = os.path.join(PREFIX_PATH, "samples/resized9.png")
    with self.assertRaises(RuntimeError):
      evaluate.predict_image(self.tflm_interpreter, wrong_size_image_path)

  def testModelAccuracy(self):
    # Test prediction accuracy on digits 0-9 using sample images
    for label in range(10):
      image_path = os.path.join(PREFIX_PATH, f"samples/sample{label}.png")
      # Run inference on the sample image
      # Note that the TFLM state is reset inside the predict_image function.
      category_probabilities = evaluate.predict_image(self.tflm_interpreter,
                                                      image_path)

      # Check the prediction result
      predicted_category = np.argmax(category_probabilities)
      self.assertEqual(predicted_category, label)


if __name__ == "__main__":
  test.main()
