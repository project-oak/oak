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

use core::ffi::c_size_t;
use std::{cell::RefCell, fs::File, io::Write, sync::Arc};

use anyhow::Context;
use libloading::{Library, Symbol};
use oak_functions_abi::{Request, Response};
use oak_functions_service::{
    lookup::{LookupData, LookupDataManager},
    Handler, Observer,
};
use ouroboros::self_referencing;
use tempfile::{tempdir, TempDir};

struct RequestContext {
    request: Vec<u8>,
    response: Vec<u8>,
    lookup_data: LookupData<16>,
}

thread_local! {
    static CONTEXT: RefCell<Option<RequestContext>> = const { RefCell::new(None) };
}

// Callbacks for the C side.
#[allow(dead_code)]
mod callbacks {
    use core::ffi::c_size_t;
    use std::{ptr, slice, str};

    use super::CONTEXT;

    /// Safety: the caller needs to guarantee that the `len` pointer is valid.
    pub unsafe extern "C" fn read_request(len: *mut c_size_t) -> *const u8 {
        CONTEXT.with(|ctx| {
            let bind = ctx.borrow();
            let ctx = bind.as_ref().expect("no currently active request!");
            *len = ctx.request.len();
            ctx.request.as_ptr()
        })
    }

    /// Safety: the caller needs to guarantee that `data` and `len` are valid.
    pub unsafe extern "C" fn write_response(data: *const u8, len: c_size_t) -> bool {
        CONTEXT.with(|ctx| {
            let mut bind = ctx.borrow_mut();
            let ctx = bind.as_mut().expect("no currently active request!");

            // Create a copy of the data.
            ctx.response = slice::from_raw_parts(data, len).into();
            true
        })
    }

    /// Safety: the caller needs to guarantee that `data` and `len` are valid.
    pub unsafe extern "C" fn log(data: *const u8, len: c_size_t) -> bool {
        CONTEXT.with(|ctx| {
            let bind = ctx.borrow();
            let ctx = bind.as_ref().expect("no currently active request!");
            match str::from_utf8(slice::from_raw_parts(data, len)) {
                Ok(message) => {
                    ctx.lookup_data.log_debug(message);
                    true
                }
                Err(_) => false,
            }
        })
    }

    /// Safety: the caller needs to guarantee `key`, `len` and `item_len` are
    /// valid. The caller is not allowed to mutate the data the returned
    /// pointer points to.
    pub unsafe extern "C" fn storage_get_item(
        key: *const u8,
        len: c_size_t,
        item_len: *mut c_size_t,
    ) -> *const u8 {
        CONTEXT.with(|ctx| {
            let bind = ctx.borrow();
            let ctx = bind.as_ref().expect("no currently active request!");
            let key = slice::from_raw_parts(key, len);
            match ctx.lookup_data.get(key) {
                Some(val) => {
                    *item_len = val.len();
                    val.as_ptr()
                }
                None => {
                    *item_len = 0;
                    ptr::null()
                }
            }
        })
    }

    /// Safety: the caller must guarantee that `status_code` and `len` are
    /// valid.
    pub unsafe extern "C" fn read_error(status_code: *mut u32, len: *mut c_size_t) -> *const u8 {
        // not entirely sure what to do here
        *status_code = micro_rpc::StatusCode::Unknown.into();
        *len = 0;
        ptr::null()
    }
}

#[self_referencing]
struct SharedLibrary {
    lib: Library,

    #[borrows(lib)]
    #[covariant]
    oak_main: Symbol<'this, unsafe extern "C" fn()>,
}

/// Variant of a Handler that dynamically loads a `.so` file and invokes native
/// code to handle requests from there.
pub struct NativeHandler {
    lookup_data_manager: Arc<LookupDataManager<16>>,

    #[allow(dead_code)]
    observer: Option<Arc<dyn Observer + Send + Sync>>,

    /// Temporary directory containing the `.so` file.
    ///
    /// This field is never read, but we need to keep it around so that the
    /// directory would be property disposed of when `NativeHandler` goes
    /// out of scope.
    #[allow(dead_code)]
    directory: TempDir,

    /// Instance of the actual shared library.
    library: SharedLibrary,
}

impl NativeHandler {
    /// Registers our callback functions with the loaded library.
    ///
    /// Safety: the library needs to export a `register_callback`` symbol with
    /// the expected semantics.
    unsafe fn register_callbacks(&self) -> anyhow::Result<()> {
        // These signatures should probably come via bindgen from the C header file in
        // the future.
        let register_callbacks =
            self.library.borrow_lib().get::<unsafe extern "C" fn(
                unsafe extern "C" fn(*mut c_size_t) -> *const u8,
                unsafe extern "C" fn(*const u8, c_size_t) -> bool,
                unsafe extern "C" fn(*const u8, c_size_t) -> bool,
                unsafe extern "C" fn(*const u8, c_size_t, *mut c_size_t) -> *const u8,
                unsafe extern "C" fn(*mut u32, *mut c_size_t) -> *const u8,
            )>("register_callbacks".as_bytes())?;

        register_callbacks(
            callbacks::read_request,
            callbacks::write_response,
            callbacks::log,
            callbacks::storage_get_item,
            callbacks::read_error,
        );

        Ok(())
    }

    /// Call the main `oak_main` function from the shared library.
    ///
    /// Safety: the library needs to export a `oak_main` symbol with the
    /// expected semantics.
    unsafe fn oak_main(&self) {
        self.library.borrow_oak_main()()
    }
}

impl Handler for NativeHandler {
    type HandlerType = NativeHandler;
    type HandlerConfig = ();

    /// Creates a new native handler.
    ///
    /// The module is expected to be a dynamically loadable shared object, which
    /// we load using `dlopen()`.
    ///
    /// Safety: It's up to the caller to guarantee that said shared object
    /// adheres to the semantics we require. This method should really be
    /// marked `unsafe` because of that.
    fn new_handler(
        _config: (),
        module_bytes: &[u8],
        lookup_data_manager: Arc<LookupDataManager<16>>,
        observer: Option<Arc<dyn Observer + Send + Sync>>,
    ) -> anyhow::Result<NativeHandler> {
        let directory = tempdir().context("could not create temporary directory")?;
        let filename = directory.path().join("module.so");
        {
            let mut file =
                File::create(&filename).context("could not open module file for writing")?;
            file.write_all(module_bytes).context("could not write module contents")?;
        }

        // Safety: this is safe as long as the library adheres to our contracts.
        let lib = unsafe { Library::new(filename) }.context("failed to load shared library")?;

        let handler = NativeHandler {
            lookup_data_manager,
            observer,
            library: SharedLibraryTryBuilder {
                lib,
                oak_main_builder: |lib| {
                    unsafe { lib.get("oak_main".as_bytes()) }
                        .context("could not find `oak_main` in shared library")
                },
            }
            .try_build()?,
            directory,
        };

        // Safety: this is safe as long as the library adheres to our contracts.
        unsafe { handler.register_callbacks() }?;

        Ok(handler)
    }

    fn handle_invoke(&self, invoke_request: Request) -> Result<Response, micro_rpc::Status> {
        // Populate a new RequestContext. The threadlocal should be empty at this point;
        // if it is not, we've somehow clashed with another thread.
        assert!(
            CONTEXT
                .replace(Some(RequestContext {
                    request: invoke_request.body,
                    response: Vec::new(),
                    lookup_data: self.lookup_data_manager.create_lookup_data(),
                }))
                .is_none(),
            "request context was not empty"
        );

        // Safety: this is safe as long as the library adheres to our contracts.
        unsafe { self.oak_main() };

        // Clean up the request memory.
        let ctx = CONTEXT.replace(None).expect("request context was empty");
        let invoke_response =
            Response::create(oak_functions_abi::StatusCode::Success, ctx.response);
        Ok(invoke_response)
    }
}
