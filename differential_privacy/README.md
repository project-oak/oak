# Differential Privacy

This crate is an unofficial partial Rust port of the Google Go Differential
Privacy library (https://github.com/google/differential-privacy). The port tries
to stay as close as possible to the structure of the upstream Go code to make it
easier to port future patches.

We currently ported only the subset of the differential privacy library that is
required the Oak Functions runtime to support the current needs for
differentially private metrics export, specifically the ability to add Laplace
noise using
[secure noise generation](https://github.com/google/differential-privacy/blob/main/common_docs/Secure_Noise_Generation.pdf).

Note all the
[caveats](https://github.com/google/differential-privacy#caveats-of-the-dp-building-block-libraries)
from the upstream library also apply to this port.
