# Train an example model using the instructions in https://www.tensorflow.org/tutorials/keras/save_and_load and https://www.tensorflow.org/guide/keras/serialization_and_saving.
import os
import sys

import tensorflow as tf
from tensorflow import keras
import keras as k

if len(sys.argv) < 2:
    exit("path to the mnist model is not given")

saved_model_path = sys.argv[1]

# Load the dataset
(train_images, train_labels), (test_images, test_labels) = keras.datasets.mnist.load_data()

train_labels = train_labels[:1000]
test_labels = test_labels[:1000]

train_images = train_images[:1000].reshape(-1, 28 * 28) / 255.0
test_images = test_images[:1000].reshape(-1, 28 * 28) / 255.0

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
