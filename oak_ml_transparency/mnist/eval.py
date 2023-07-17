#
# Copyright 2023 The Project Oak Authors
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
#

import argparse
import json
import os
import shutil
import tarfile

import numpy as np
import tensorflow as tf
from tensorflow import keras

from cleverhans.tf2.attacks.fast_gradient_method import fast_gradient_method
from cleverhans.tf2.attacks.projected_gradient_descent import projected_gradient_descent

EPS = 0.01

def evaluate_model(mnist_path: str) -> dict:
    # Load the mnist model
    mnist_model = keras.models.load_model(mnist_path)
    print("Successfully loaded the model from", mnist_path)

    # Load some dataset to use as input to the model and for generating adversarial examples.
    (train_images, train_labels), (test_images, test_labels) = tf.keras.datasets.mnist.load_data()
    test_images = test_images[:10].reshape(-1, 28 * 28) / 255.0

    print("Input shape: ", test_images.shape)
    out = mnist_model.predict(test_images)

    # Generate adversarial examples from the input data, and get predictions for them. 
    # Based on https://github.com/cleverhans-lab/cleverhans/blob/master/tutorials/jax/mnist_tutorial.py

    y_pred_fgm = []
    y_pred_pgd = []

    for i in range(10):
        x = test_images[i:i+1]
        y = test_labels[i:i+1]
        x_fgm = fast_gradient_method(mnist_model, x, EPS, np.inf)
        y_pred_fgm.append(mnist_model(x_fgm).numpy()[0])

        x_pgd = projected_gradient_descent(mnist_model, x, EPS, 0.01, 40, np.inf)
        y_pred_pgd.append(mnist_model(x_pgd).numpy()[0])

    # Compute accuracy
    metric = tf.keras.metrics.SparseCategoricalAccuracy()
    metric.update_state(test_labels[:10], out)
    test_acc = metric.result().numpy() * 100

    metric.reset_state()
    metric.update_state(test_labels[:10], y_pred_fgm)
    fgm_acc = metric.result().numpy() * 100

    metric.reset_state()
    metric.update_state(test_labels[:10], y_pred_pgd)
    pgd_acc = metric.result().numpy() * 100
    
    result = {
        "test_acc": test_acc,
        "fgm_acc": fgm_acc,
        "pgd_acc": pgd_acc
    }
    return result

def cleanup_archive(file: tarfile.TarFile):
    for member in file.getmembers():
        if os.path.isdir(member.name):
            shutil.rmtree(member.name, ignore_errors=True)
        elif os.path.exists(member.name):
            os.remove(member.name)
    file.close()

def main():
    parser = argparse.ArgumentParser(
        allow_abbrev=False,
        prog='MNIST evaluation',
        description='Evaluates an MNIST model against adversarial examples')

    parser.add_argument('--model', help="the model as a compressed tar archive")
    parser.add_argument('--output', help="path to store the evaluation result in") 

    args = parser.parse_args()
    model_path = args.model
    output_path = args.output
    
    # Load the tar archive and decompress in the current working directory.
    file = tarfile.open(model_path)
    mnist_path = file.getmembers()[0].name
    file.extractall()

    result = evaluate_model(mnist_path)
    cleanup_archive(file)
     
    # Serialize as json
    json_object = json.dumps(result, indent=4)
    
    # Write to file at the given output path
    with open(output_path, "w") as outfile:
        outfile.write(json_object)


if __name__ == "__main__":
    main()
