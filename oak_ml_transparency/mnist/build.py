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

# Train an example model using the instructions in
# https://www.tensorflow.org/tutorials/keras/save_and_load and
# https://www.tensorflow.org/guide/keras/serialization_and_saving.

import argparse

import tensorflow as tf
from tensorflow import keras
import keras as k

# Define a simple sequential model
def create_model():
    inputs = keras.Input(shape=(784,))
    layer1 = keras.layers.Dense(512, activation='relu')(inputs)
    layer2 = keras.layers.Dropout(0.2)(layer1)
    outputs = keras.layers.Dense(10)(layer2)

    model = keras.Model(inputs, outputs)
    model.compile(optimizer='adam',
                loss=keras.losses.SparseCategoricalCrossentropy(from_logits=True),
                metrics=[keras.metrics.SparseCategoricalAccuracy()])
    
    return model

def main():
    parser = argparse.ArgumentParser(
        allow_abbrev=False,
        prog='MNIST build',
        description='Trains an MNIST model and stores it in the given path')

    parser.add_argument('--output', help="path to store the model, as a SavedModel format") 

    args = parser.parse_args()
    saved_model_path = args.output

    # Load the dataset
    (train_images, train_labels), (test_images, test_labels) = keras.datasets.mnist.load_data()

    train_labels = train_labels[:1000]
    train_images = train_images[:1000].reshape(-1, 28 * 28) / 255.0

    test_labels = test_labels[1000:]
    test_images = test_images[1000:].reshape(-1, 28 * 28) / 255.0

    # Create a basic model instance
    model = create_model()

    # Display the model's architecture
    model.summary()

    # Train the model
    model.fit(train_images, 
            train_labels,  
            epochs=10,
            validation_data=(test_images, test_labels)
            ) 

    print(f"Training completed; saving the model in {saved_model_path}...")
    model.save(saved_model_path)

if __name__ == "__main__":
    main()
