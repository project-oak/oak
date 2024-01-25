//
// Copyright 2024 The Project Oak Authors
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

#![feature(never_type)]
#![feature(result_flattening)]
#![feature(array_chunks)]

use oak_launcher_utils::{
    channel::{self},
    launcher,
};

pub async fn create(
    params: launcher::Params,
) -> Result<(Box<dyn launcher::GuestInstance>, channel::ConnectorHandle), Box<dyn std::error::Error>>
{
    log::info!("creating guest instance");
    launcher::launch(params).await
}
