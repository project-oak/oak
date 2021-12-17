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

use crate::{
    logger::Logger, lookup::LookupFactory, lookup_data::LookupData, server::BoxedExtensionFactory,
};
use std::sync::Arc;

/// Create and return a lookup factory.
pub async fn create_lookup_factory(
    lookup_data: Arc<LookupData>,
    logger: Logger,
) -> anyhow::Result<BoxedExtensionFactory> {
    let lookup_factory = LookupFactory::new(lookup_data, logger)?;
    let lookup_factory: BoxedExtensionFactory = Box::new(lookup_factory);
    Ok(lookup_factory)
}
