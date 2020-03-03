pub mod mutex;
pub mod thread;

// TODO(#659): Add/update primitives provided
pub struct RwLock<T>{_x:core::marker::PhantomData<T>}
pub use mutex::Mutex;
