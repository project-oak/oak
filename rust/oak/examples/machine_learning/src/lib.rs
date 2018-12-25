//
// Copyright 2018 The Project Oak Authors
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

// This model was inspired by
// https://github.com/AtheMathmo/rusty-machine/blob/master/examples/naive_bayes_dogs.rs .

extern crate oak;
extern crate rand;
extern crate rusty_machine;

use rand::distributions::Distribution;
use rand::distributions::Normal;
use rand::distributions::Standard;
use rand::prelude::*;
use rusty_machine::learning::naive_bayes::{self, NaiveBayes};
use rusty_machine::learning::SupModel;
use rusty_machine::linalg::{BaseMatrix, Matrix};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Type {
    Cat,
    Dog,
}

#[derive(Clone, Debug)]
struct Animal {
    type_: Type,
    friendliness: f64,
    furriness: f64,
    speed: f64,
}

impl Distribution<Animal> for Standard {
    /// Generate a random animal.
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Animal {
        // Friendliness, furriness, and speed are normally distributed and (given type) independent.
        let mut cat_friendliness = Normal::new(0., 1.);
        let mut cat_furriness = Normal::new(0., 1.);
        let mut cat_speed = Normal::new(0., 1.);

        let mut dog_friendliness = Normal::new(1., 1.);
        let mut dog_furriness = Normal::new(1., 1.);
        let mut dog_speed = Normal::new(-1., 1.);

        // Flip a coin to decide whether to generate a cat or a dog.
        let coin: f64 = rng.gen();
        let color = if coin < 0.5 { Type::Cat } else { Type::Dog };

        match color {
            Type::Cat => Animal {
                type_: Type::Cat,
                friendliness: cat_friendliness.sample(rng),
                furriness: cat_furriness.sample(rng),
                speed: cat_speed.sample(rng),
            },
            Type::Dog => Animal {
                type_: Type::Dog,
                friendliness: dog_friendliness.sample(rng),
                furriness: dog_furriness.sample(rng),
                speed: dog_speed.sample(rng),
            },
        }
    }
}

fn generate_animal_data(
    training_set_size: u32,
    test_set_size: u32,
) -> (Matrix<f64>, Matrix<f64>, Matrix<f64>, Vec<Animal>) {
    oak::print("rnd xxx\n");
    //let mut rng = rand::thread_rng();
    let mut rng = rand::StdRng::seed_from_u64(123);
    oak::print("rnd OK\n");

    // We'll train the model on these dogs
    let training_animals = (0..training_set_size)
        .map(|_| rng.gen())
        .collect::<Vec<Animal>>();

    // ... and then use the model to make predictions about these dogs' color
    // given only their trait measurements.
    let test_animals = (0..test_set_size)
        .map(|_| rng.gen())
        .collect::<Vec<Animal>>();

    // The model's `.train` method will take two matrices, each with a row for
    // each dog in the training set: the rows in the first matrix contain the
    // trait measurements; the rows in the second are either [1, 0] or [0, 1]
    // to indicate color.
    let training_data: Vec<f64> = training_animals
        .iter()
        .flat_map(|animal| vec![animal.friendliness, animal.furriness, animal.speed])
        .collect();
    let training_matrix: Matrix<f64> = training_data.chunks(3).collect();
    let target_data: Vec<f64> = training_animals
        .iter()
        .flat_map(|animal| match animal.type_ {
            Type::Cat => vec![1., 0.],
            Type::Dog => vec![0., 1.],
        })
        .collect();
    let target_matrix: Matrix<f64> = target_data.chunks(2).collect();

    // Build another matrix for the test set of dogs to make predictions about.
    let test_data: Vec<f64> = test_animals
        .iter()
        .flat_map(|animal| vec![animal.friendliness, animal.furriness, animal.speed])
        .collect();
    let test_matrix: Matrix<f64> = test_data.chunks(3).collect();

    (training_matrix, target_matrix, test_matrix, test_animals)
}

fn evaluate_prediction(hits: &mut u32, animal: &Animal, prediction: &[f64]) -> (Type, bool) {
    let predicted_type = animal.type_;
    let actual_type = if prediction[0] == 1. {
        Type::Cat
    } else {
        Type::Dog
    };
    let accurate = predicted_type == actual_type;
    if accurate {
        *hits += 1;
    }
    (actual_type, accurate)
}

#[no_mangle]
pub extern "C" fn oak_main() {
    oak::print("Start\n");
    let (training_set_size, test_set_size) = (1000, 1000);
    // Generate all of our train and test data
    let (training_matrix, target_matrix, test_matrix, test_animals) =
        generate_animal_data(training_set_size, test_set_size);

    oak::print("Training model\n");
    let mut model = NaiveBayes::<naive_bayes::Gaussian>::new();
    model
        .train(&training_matrix, &target_matrix)
        .expect("failed to train model of dogs");

    oak::print("Predicting\n");
    let predictions = model
        .predict(&test_matrix)
        .expect("failed to predict dogs!?");

    // Score how well we did.
    let mut hits = 0;
    let unprinted_total = test_set_size.saturating_sub(10) as usize;
    for (animal, prediction) in test_animals
        .iter()
        .zip(predictions.iter_rows())
        .take(unprinted_total)
    {
        evaluate_prediction(&mut hits, animal, prediction);
    }

    if unprinted_total > 0 {
        println!("...");
    }

    for (animal, prediction) in test_animals
        .iter()
        .zip(predictions.iter_rows())
        .skip(unprinted_total)
    {
        let (actual_type, accurate) = evaluate_prediction(&mut hits, animal, prediction);
        println!(
            "Predicted: {:?}; Actual: {:?}; Accurate? {:?}",
            animal.type_, actual_type, accurate
        );
    }

    oak::print(&format!(
        "Accuracy: {}/{} = {:.1}%",
        hits,
        test_set_size,
        (f64::from(hits)) / (f64::from(test_set_size)) * 100.
    ));
}
