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

//! Oak Functions extensions for implementing new functionality and enabling or disabling them.

/// Train for implementing extensions.
pub trait OakApiNativeExtension {
    // Similar to wasmi::Externals, but with additional optionality.
    fn invoke_index(
        &self,
        &mut wasm_state: WasmState,
        args: wasmi::RuntimeArgs,
    ) -> Option<Result<Option<wasmi::RuntimeValue>, wasmi::Trap>>;

    // Similar to wasmi::ModuleImportResolver, but with additional optionality.
    fn resolve_func(&self) -> Option<Result<wasmi::FuncRef, wasmi::Error>>;

    fn register_index(&mut self, index: usize);
}
