//
// Copyright 2021 The Project Oak Authors
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

//! Utilities to fetch, parse and process MNIST data. Inspired by
//! https://github.com/tensorflow/serving/blob/f3fbec59798e13cb1f7230fcf891c0ec4113331e/tensorflow_serving/example/mnist_input_data.py

use crate::proto::{tensor_shape_proto::Dim, DataType, TensorProto, TensorShapeProto};
use anyhow::Context;
use flate2::read::GzDecoder;
use log::{debug, info};
use std::{
    fs::{read, write},
    io::Read,
    path::PathBuf,
};

// CVDF mirror of http://yann.lecun.com/exdb/mnist/
static SOURCE_URL: &str = "https://storage.googleapis.com/cvdf-datasets/mnist/";
static TEST_IMAGES: &str = "t10k-images-idx3-ubyte.gz";
static TEST_LABELS: &str = "t10k-labels-idx1-ubyte.gz";

/// Wrapper for linking an image to its expected label.
pub struct DataItem {
    pub image: TensorProto,
    pub label: u8,
}

/// A collection of images that all have the same width and height.
pub struct Images {
    /// The data for each of the images. Each image is represented as a vector of grayscale pixel
    /// values.
    items: Vec<Vec<u8>>,
    /// The height of each of the images in pixels.
    rows: usize,
    /// The width of each of the images in pixels.
    cols: usize,
}

/// An image data set used for testing.
pub struct DataSet {
    images: Images,
    labels: Vec<u8>,
}

impl DataSet {
    pub fn iter(&self) -> Iter {
        Iter {
            data: self,
            current_index: 0,
        }
    }
}

/// Iterator to iterate over the items in the dataset.
pub struct Iter<'a> {
    data: &'a DataSet,
    current_index: usize,
}

impl std::iter::Iterator for Iter<'_> {
    type Item = DataItem;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index >= self.data.labels.len()
            || self.current_index >= self.data.images.items.len()
        {
            return None;
        }

        let label = self.data.labels[self.current_index];
        let image = new_image_tensor_proto(
            &self.data.images.items[self.current_index],
            self.data.images.rows,
            self.data.images.cols,
        );
        self.current_index += 1;

        Some(DataItem { image, label })
    }
}

fn new_image_tensor_proto(image: &[u8], rows: usize, cols: usize) -> TensorProto {
    // We convert the grayscale pixels from a u8 to an f32 between 0.0 and 1.0.
    let float_val = image
        .iter()
        .map(|pixel| (*pixel as f32) / 255.)
        .collect::<Vec<f32>>();
    debug!("number of values: {}", float_val.len());

    let tensor_shape = Some(TensorShapeProto {
        dim: vec![
            Dim {
                size: 1,
                name: String::default(),
            },
            Dim {
                size: (rows * cols) as i64,
                name: String::default(),
            },
        ],
        unknown_rank: false,
    });
    debug!("tensor shape: {:?}", tensor_shape);

    TensorProto {
        dtype: DataType::DtFloat as i32,
        tensor_shape,
        version_number: 0,
        float_val,
        ..Default::default()
    }
}

/// Gets the test data by parsing the data files. It will first look for the data files in
/// `work_dir`. If the files are not there, it will download them and save copies in `work_dir`.
pub async fn get_test_data(work_dir: &str) -> anyhow::Result<DataSet> {
    let image_buffer = get_uncompressed(work_dir, TEST_IMAGES)
        .await
        .context("couldn't get images")?;
    let label_buffer = get_uncompressed(work_dir, TEST_LABELS)
        .await
        .context("couldn't get labels")?;
    let images = parse_images(&image_buffer).context("couldn't parse image buffer")?;
    let labels = parse_labels(&label_buffer).context("couldn't parse label buffer")?;
    if images.items.len() != labels.len() {
        anyhow::bail!("number of images and labels do not match");
    }
    Ok(DataSet { images, labels })
}

fn parse_images(image_buffer: &[u8]) -> anyhow::Result<Images> {
    // The images file starts with 16 bytes that represent a magic number, the number of images,
    // number of rows and number of columns, each encoded as a big endian u32. The rest of bytes
    // represent grayscale pixel brightness as a u8 arranged by row for each image.
    // See https://deepai.org/dataset/mnist
    let magic = read_be_u32(&image_buffer[..4]).context("couldn't read magic number")? as usize;
    if magic != 2051 {
        anyhow::bail!("magic number is invalid; {}", magic);
    }
    let num_images =
        read_be_u32(&image_buffer[4..8]).context("couldn't read number of images")? as usize;
    info!("number of images: {}", num_images);
    let rows = read_be_u32(&image_buffer[8..12])
        .context("couldn't read number of rows per image")? as usize;
    info!("number of rows: {}", rows);
    let cols = read_be_u32(&image_buffer[12..16])
        .context("couldn't read number of columns per image")? as usize;
    info!("number of cols: {}", cols);
    if image_buffer.len() != num_images * rows * cols + 16_usize {
        anyhow::bail!("image buffer is invalid");
    }

    let items = image_buffer[16..]
        .chunks(rows * cols)
        .map(|chunk| chunk.to_vec())
        .collect::<Vec<Vec<u8>>>();

    Ok(Images { items, rows, cols })
}

fn parse_labels(label_buffer: &[u8]) -> anyhow::Result<Vec<u8>> {
    // The labels file starts with 8 bytes that represent a magic number and the number of labels,
    // each encoded as a big endian u32. The rest of the bytes represent a u8 value for each
    // example.
    // See https://deepai.org/dataset/mnist
    let magic = read_be_u32(&label_buffer[..4]).context("couldn't read magic number")? as usize;
    if magic != 2049 {
        anyhow::bail!("magic number is invalid; {}", magic);
    }
    let num_labels =
        read_be_u32(&label_buffer[4..8]).context("couldn't read number of labels")? as usize;
    info!("number of labels: {}", num_labels);
    if label_buffer.len() != num_labels + 8_usize {
        anyhow::bail!("label buffer is invalid");
    }
    Ok(label_buffer[8..].to_vec())
}

fn read_be_u32(buffer: &[u8]) -> anyhow::Result<u32> {
    if buffer.len() != 4 {
        anyhow::bail!("buffer is not 4 bytes");
    }
    let mut num_bytes = [0; 4];
    num_bytes.copy_from_slice(buffer);
    Ok(u32::from_be_bytes(num_bytes))
}

/// Gets the data file and decompresses it. Data files are compressed using the gzip format.
async fn get_uncompressed(work_dir: &str, file_name: &str) -> anyhow::Result<Vec<u8>> {
    let compressed_file = maybe_download(work_dir, file_name)
        .await
        .context("couldn't get compressed file")?;
    info!("compressed file size: {}", compressed_file.len());

    let mut decoder = GzDecoder::new(&compressed_file[..]);
    let mut bytes = Vec::new();
    decoder
        .read_to_end(&mut bytes)
        .context("couldn't decompress file")?;
    info!("uncompressed file size: {}", bytes.len());
    Ok(bytes)
}

async fn maybe_download(work_dir: &str, file_name: &str) -> anyhow::Result<Vec<u8>> {
    let mut path = PathBuf::from(work_dir);
    path.push(file_name);
    if path.exists() {
        info!("reading local file: {}", path.display());
        read(path).context("couldn't read file")
    } else {
        info!("downloading file: {}{}", SOURCE_URL, file_name);
        let bytes = reqwest::get(format!("{}{}", SOURCE_URL, file_name))
            .await
            .context("couldn't download file")?
            .bytes()
            .await
            .context("couldn't get contente from downloaded file")?
            .to_vec();
        write(path, &bytes).context("couldn't write downloaded file")?;
        Ok(bytes.to_vec())
    }
}
