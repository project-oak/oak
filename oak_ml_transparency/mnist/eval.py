import sys

import numpy as np
import tensorflow as tf
from tensorflow import keras

from cleverhans.tf2.attacks.fast_gradient_method import fast_gradient_method
from cleverhans.tf2.attacks.projected_gradient_descent import projected_gradient_descent

EPS = 0.01

if len(sys.argv) < 2:
    exit("path to the mnist model is not given")

mnist_path = sys.argv[1]

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
acc = metric.result().numpy() * 100
print(f"Accuracy on test:{acc:54.2f}%")

metric.reset_state()
metric.update_state(test_labels[:10], y_pred_fgm)
acc = metric.result().numpy() * 100
print(f"Accuracy on adversarial examples from fast gradient method:{acc:12.2f}%")

metric.reset_state()
metric.update_state(test_labels[:10], y_pred_pgd)
acc = metric.result().numpy() * 100
print(f"Accuracy on adversarial examples from projected gradient descent:{acc:6.2f}%")
