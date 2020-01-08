// Copyright 2018 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! Encoding contains functions and traits for FIDL2 encoding and decoding.

use {
    crate::handle::{Handle, HandleBased, MessageBuf},
    crate::{Error, Result},
    bitflags::bitflags,
    byteorder::{ByteOrder, LittleEndian},
    fuchsia_zircon_status as zx_status,
    std::{cell::RefCell, cmp, mem, ptr, str, u32, u64},
};

thread_local!(static CODING_BUF: RefCell<MessageBuf> = RefCell::new(MessageBuf::new()));

/// Acquire a mutable reference to the thread-local encoding buffers.
///
/// This function may not be called recursively.
pub fn with_tls_coding_bufs<R>(f: impl FnOnce(&mut Vec<u8>, &mut Vec<Handle>) -> R) -> R {
    CODING_BUF.with(|buf| {
        let mut buf = buf.borrow_mut();
        let (bytes, handles) = buf.split_mut();
        let res = f(bytes, handles);
        buf.clear();
        res
    })
}

/// Encodes the provided type into the thread-local encoding buffers.
///
/// This function may not be called recursively.
pub fn with_tls_encoded<T, E: From<Error>>(
    val: &mut impl Encodable,
    f: impl FnOnce(&mut Vec<u8>, &mut Vec<Handle>) -> std::result::Result<T, E>,
) -> std::result::Result<T, E> {
    with_tls_coding_bufs(|bytes, handles| {
        Encoder::encode(bytes, handles, val)?;
        f(bytes, handles)
    })
}

/// Rounds `x` up if necessary so that it is a multiple of `align`.
pub fn round_up_to_align(x: usize, align: usize) -> usize {
    if align == 0 {
        x
    } else {
        ((x + align - 1) / align) * align
    }
}

/// Split off the first element from a slice.
fn split_off_first<'a, T>(slice: &mut &'a [T]) -> Result<&'a T> {
    split_off_front(slice, 1).map(|res| &res[0])
}

/// Split off the first element from a mutable slice.
fn split_off_first_mut<'a, T>(slice: &mut &'a mut [T]) -> Result<&'a mut T> {
    split_off_front_mut(slice, 1).map(|res| &mut res[0])
}

/// Split of the first `n` bytes from `slice`.
fn split_off_front<'a, T>(slice: &mut &'a [T], n: usize) -> Result<&'a [T]> {
    if n > slice.len() {
        return Err(Error::OutOfRange);
    }
    let original = take_slice(slice);
    let (head, tail) = original.split_at(n);
    *slice = tail;
    Ok(head)
}

/// Split of the first `n` mutable bytes from `slice`.
fn split_off_front_mut<'a, T>(slice: &mut &'a mut [T], n: usize) -> Result<&'a mut [T]> {
    if n > slice.len() {
        return Err(Error::OutOfRange);
    }
    let original = take_slice_mut(slice);
    let (head, tail) = original.split_at_mut(n);
    *slice = tail;
    Ok(head)
}

/// Empty out a slice.
fn take_slice<'a, T>(x: &mut &'a [T]) -> &'a [T] {
    mem::replace(x, &mut [])
}

/// Empty out a mutable slice.
fn take_slice_mut<'a, T>(x: &mut &'a mut [T]) -> &'a mut [T] {
    mem::replace(x, &mut [])
}

#[doc(hidden)] // only exported for macro use
pub fn take_handle<T: HandleBased>(handle: &mut T) -> Handle {
    let invalid = T::from_handle(Handle::invalid());
    mem::replace(handle, invalid).into_handle()
}

/// The maximum recursion depth of encoding and decoding.
/// Each nested aggregate type (structs, unions, arrays, or vectors) counts as one step in the
/// recursion depth.
pub const MAX_RECURSION: usize = 32;

/// Indicates that an optional value is present.
pub const ALLOC_PRESENT_U64: u64 = u64::MAX;
/// Indicates that an optional value is present.
pub const ALLOC_PRESENT_U32: u32 = u32::MAX;
/// Indicates that an optional value is absent.
pub const ALLOC_ABSENT_U64: u64 = 0;
/// Indicates that an optional value is absent.
pub const ALLOC_ABSENT_U32: u32 = 0;

/// Special ordinal signifying an epitaph message.
pub const EPITAPH_ORDINAL: u64 = 0xffffffffffffffffu64;

/// The current wire format magic number
pub const MAGIC_NUMBER_INITIAL: u8 = 1;

/// Context for encoding and decoding.
///
/// This is currently empty. We keep it around to ease the implementation of
/// context-dependent behavior for future migrations.
///
/// WARNING: Do not construct this directly unless you know what you're doing.
/// FIDL uses `Context` to coordinate soft migrations, so improper uses of it
/// could result in ABI breakage.
#[derive(Clone, Copy, Debug)]
pub struct Context {}

impl Context {
    /// Returns the header flags to set when encoding with this context.
    fn header_flags(&self) -> HeaderFlags {
        HeaderFlags::UNIONS_USE_XUNION_FORMAT
    }
}

/// Encoding state
#[derive(Debug)]
pub struct Encoder<'a> {
    /// Offset at which to write new objects.
    offset: usize,

    /// The maximum remaining number of recursive steps.
    remaining_depth: usize,

    /// Buffer to write output data into.
    ///
    /// New chunks of out-of-line data should be appended to the end of the `Vec`.
    /// `buf` should be resized to be large enough for any new data *prior* to encoding the inline
    /// portion of that data.
    buf: &'a mut Vec<u8>,

    /// Buffer to write output handles into.
    handles: &'a mut Vec<Handle>,

    /// Encoding context.
    context: Context,
}

/// Decoding state
#[derive(Debug)]
pub struct Decoder<'a> {
    /// The maximum remaining number of recursive steps.
    remaining_depth: usize,

    /// Buffer from which to read data for the inline part of the message.
    buf: &'a [u8],

    /// Original length of the buf slice. Used to report error messages. A difference between this
    /// value and buf.len() is the current decoding position for the inline part of the message.
    initial_buf_len: usize,

    /// Buffer from which to read out-of-line data.
    out_of_line_buf: &'a [u8],

    /// Original length of the out_of_line_buf slice. Used to report error messages. A difference
    /// between this value and out_of_line_buf.len() is the current decoding position for the
    /// out-of-line part of the message.
    initial_out_of_line_buf_len: usize,

    /// Buffer from which to read handles.
    handles: &'a mut [Handle],

    /// Decoding context.
    context: Context,
}

/// The default context for encoding.
fn default_encode_context() -> Context {
    // During migrations, this controls the default write path.
    Context {}
}

impl<'a> Encoder<'a> {
    /// FIDL2-encodes `x` into the provided data and handle buffers.
    pub fn encode<T: Encodable + ?Sized>(
        buf: &'a mut Vec<u8>,
        handles: &'a mut Vec<Handle>,
        x: &mut T,
    ) -> Result<()> {
        let context = default_encode_context();
        Self::encode_with_context(&context, buf, handles, x)
    }

    /// FIDL2-encodes `x` into the provided data and handle buffers, using the
    /// specified encoding context.
    ///
    /// WARNING: Do not call this directly unless you know what you're doing.
    /// FIDL uses `Context` to coordinate soft migrations, so improper uses of
    /// this function could result in ABI breakage.
    pub fn encode_with_context<T: Encodable + ?Sized>(
        context: &Context,
        buf: &'a mut Vec<u8>,
        handles: &'a mut Vec<Handle>,
        x: &mut T,
    ) -> Result<()> {
        fn prepare_for_encoding<'a>(
            context: &Context,
            buf: &'a mut Vec<u8>,
            handles: &'a mut Vec<Handle>,
            ty_inline_size: usize,
        ) -> Encoder<'a> {
            let inline_size = round_up_to_align(ty_inline_size, 8);
            buf.truncate(0);
            buf.resize(inline_size, 0);
            handles.truncate(0);
            Encoder { offset: 0, remaining_depth: MAX_RECURSION, buf, handles, context: *context }
        }

        let mut encoder = prepare_for_encoding(context, buf, handles, x.inline_size(context));
        x.encode(&mut encoder)
    }

    /// Runs the provided closure at at the next recursion depth level,
    /// erroring if the maximum recursion limit has been reached.
    pub fn recurse<F, R>(&mut self, f: F) -> Result<R>
    where
        F: FnOnce(&mut Encoder<'_>) -> Result<R>,
    {
        if self.remaining_depth == 0 {
            return Err(Error::MaxRecursionDepth);
        }

        self.remaining_depth -= 1;
        let res = f(self)?;
        self.remaining_depth += 1;
        Ok(res)
    }

    /// Returns a slice of the next `len` bytes after `offset` and increases `offset` by `len`.
    pub fn next_slice(&mut self, len: usize) -> Result<&mut [u8]> {
        let ret = self.buf.get_mut(self.offset..(self.offset + len)).ok_or(Error::OutOfRange)?;
        self.offset += len;
        Ok(ret)
    }

    /// Adds specified number of zero bytes as padding.  Effectively, just increases `offset` by
    /// `len`.
    pub fn padding(&mut self, len: usize) -> Result<()> {
        if self.offset + len > self.buf.len() {
            return Err(Error::OutOfRange);
        }
        self.offset += len;
        Ok(())
    }

    /// Returns the inline alignment of an object of type `Target` for this encoder.
    pub fn inline_align_of<Target: Encodable>(&self) -> usize {
        <Target as Layout>::inline_align(&self.context)
    }

    /// Returns the inline size of the given object for this encoder.
    pub fn inline_size_of<Target: Encodable>(&self) -> usize {
        <Target as Layout>::inline_size(&self.context)
    }

    /// Adds as many zero bytes as padding as necessary to make sure that the
    /// `target` object size is equal to `inline_size_of::<Target>()`.
    /// `start_pos` is the position in the `encoder` buffer of where the
    /// encoding started. See `Encoder::offset`.
    pub fn tail_padding<Target: Encodable>(&mut self, start_pos: usize) -> Result<()> {
        self.tail_padding_inner(self.inline_size_of::<Target>(), start_pos)
    }

    fn tail_padding_inner(&mut self, target_inline_size: usize, start_pos: usize) -> Result<()> {
        debug_assert!(start_pos <= self.offset);
        self.padding(target_inline_size - (self.offset - start_pos))
    }

    /// Runs the provided closure inside an encoder modified
    /// to write the data out-of-line.
    ///
    /// Once the closure has completed, this function resets the offset
    /// to where it was at the beginning of the call.
    pub fn write_out_of_line<F>(&mut self, len: usize, f: F) -> Result<()>
    where
        F: FnOnce(&mut Encoder<'_>) -> Result<()>,
    {
        let old_offset = self.offset;
        self.offset = self.buf.len();
        // Create space for the new data
        self.reserve_out_of_line(len);
        f(self)?;
        self.offset = old_offset;
        Ok(())
    }

    fn reserve_out_of_line(&mut self, len: usize) {
        self.buf.resize(self.offset + round_up_to_align(len, 8), 0);
    }

    /// Append bytes to the very end (out-of-line) of the buffer.
    pub fn append_bytes(&mut self, bytes: &[u8]) {
        let new_len = round_up_to_align(self.buf.len(), 8);
        self.buf.resize(new_len, 0);
        self.buf.extend_from_slice(bytes);
    }

    /// Append handles to the buffer.
    pub fn append_handles(&mut self, handles: &mut [Handle]) {
        self.handles.reserve(handles.len());
        for handle in handles {
            self.handles.push(take_handle(handle));
        }
    }

    /// Returns the encoder's context.
    pub fn context(&self) -> &Context {
        &self.context
    }
}

impl<'a> Decoder<'a> {
    /// FIDL2-decodes a value of type `T` from the provided data and handle
    /// buffers. Assumes the buffers came from inside a transaction message
    /// wrapped by `header`.
    pub fn decode_into<T: Decodable>(
        header: &TransactionHeader,
        buf: &'a [u8],
        handles: &'a mut [Handle],
        value: &mut T,
    ) -> Result<()> {
        Self::decode_with_context(&header.decoding_context(), buf, handles, value)
    }

    /// FIDL2-decodes a value of type `T` from the provided data and handle
    /// buffers, using the specified context.
    ///
    /// WARNING: Do not call this directly unless you know what you're doing.
    /// FIDL uses `Context` to coordinate soft migrations, so improper uses of
    /// this function could result in ABI breakage.
    pub fn decode_with_context<T: Decodable>(
        context: &Context,
        buf: &'a [u8],
        handles: &'a mut [Handle],
        value: &mut T,
    ) -> Result<()> {
        let inline_size = T::inline_size(context);
        let out_of_line_offset = round_up_to_align(inline_size, 8);
        if buf.len() < out_of_line_offset {
            return Err(Error::OutOfRange);
        }

        let (buf, out_of_line_buf) = buf.split_at(out_of_line_offset);

        let mut decoder = Decoder {
            remaining_depth: MAX_RECURSION,
            buf,
            initial_buf_len: buf.len(),
            out_of_line_buf,
            initial_out_of_line_buf_len: out_of_line_buf.len(),
            handles,
            context: *context,
        };
        value.decode(&mut decoder)?;
        if decoder.out_of_line_buf.len() != 0 {
            return Err(Error::ExtraBytes);
        }
        if decoder.handles.len() != 0 {
            return Err(Error::ExtraHandles);
        }
        debug_assert!(
            decoder.buf.len() == out_of_line_offset - inline_size,
            "Inline part of the buffer was not completely consumed. Most likely, this indicates a \
             bug in the FIDL decoders.\n\
             Inline buffer size: {}\n\
             Type size: {}\n\
             Consumed: {}\n\
             Leftover size: {}\n\
             Buffer: {:X?}",
            out_of_line_offset,
            inline_size,
            out_of_line_offset - decoder.buf.len(),
            decoder.buf.len(),
            decoder.buf,
        );
        for i in 0..decoder.buf.len() {
            if decoder.buf[i] != 0 {
                return Err(Error::NonZeroPadding {
                    padding_start: inline_size,
                    non_zero_pos: inline_size + i,
                });
            }
        }
        Ok(())
    }

    /// Runs the provided closure at at the next recursion depth level,
    /// erroring if the maximum recursion limit has been reached.
    pub fn recurse<F, R>(&mut self, f: F) -> Result<R>
    where
        F: FnOnce(&mut Decoder<'_>) -> Result<R>,
    {
        if self.remaining_depth == 0 {
            return Err(Error::MaxRecursionDepth);
        }

        self.remaining_depth -= 1;
        let res = f(self)?;
        self.remaining_depth += 1;
        Ok(res)
    }

    /// Runs the provided closure inside an decoder modified
    /// to read out-of-line data.
    ///
    /// `absolute_offset` indicates the offset of the start of the out-of-line data to read,
    /// relative to the original start of the buffer.
    pub fn read_out_of_line<F, R>(&mut self, len: usize, f: F) -> Result<R>
    where
        F: FnOnce(&mut Decoder<'_>) -> Result<R>,
    {
        let (old_buf, old_initial_buf_len) = self.before_read_out_of_line(len)?;
        let res = f(self);

        // Set the current `buf` back to its original position.
        //
        // After this transformation, the final `Decoder` looks like this:
        // [---------------------------------]
        //     ^---buf--^               ^ool^ (slices)
        //                              ^out-of-line-advanced (index)
        self.buf = old_buf;
        self.initial_buf_len = old_initial_buf_len;
        res
    }

    // Returns old_buf and old_initial_buf_len
    fn before_read_out_of_line(&mut self, len: usize) -> Result<(&'a [u8], usize)> {
        // Currently, out-of-line points here:
        // [---------------------------------]
        //     ^---buf--^    ^-out-of-line--^ (slices)
        //
        // We want to shift so that `buf` points to the first `len` bytes in `out-of-line` that
        // are aligned to `align`, and `old-buf` points to the previous value of `buf`:
        //
        // [---------------------------------]
        //     ^old--buf^      ^--buf--^^ool^
        //
        // We also adjust the initial_buf_len, so that the index of an invalid byte can still be
        // comupted using the same formula: initial_buf_len - buf.len().

        // We split off the first `len` bytes from `out_of_line`.
        let new_buf = split_off_front(&mut self.out_of_line_buf, len)?;
        let new_initial_buf_len =
            self.initial_buf_len + self.initial_out_of_line_buf_len - self.out_of_line_buf.len();
        // Split off any trailing bytes up to the alignment and discard them.
        if len % 8 != 0 {
            let trailer = 8 - (len % 8);
            let _ = split_off_front(&mut self.out_of_line_buf, trailer)?;
        }

        // Store the current `buf` slice and shift the `buf` slice to point at the out-of-line data.
        let old_buf = take_slice(&mut self.buf);
        let old_initial_buf_len = self.initial_buf_len;
        self.buf = new_buf;
        self.initial_buf_len = new_initial_buf_len;

        Ok((old_buf, old_initial_buf_len))
    }

    /// Whether or not the current section of inline bytes has been fully read.
    pub fn is_empty(&self) -> bool {
        self.buf.is_empty()
    }

    /// Current decoding position in the inline part of the message, counting from the original
    /// first byte passed to `decode_into`.
    pub fn inline_pos(&self) -> usize {
        self.initial_buf_len - self.buf.len()
    }

    /// Current decoding position in the out-of-line part of the message, counting from the
    /// original first byte passed to `decode_into`.
    pub fn out_of_line_pos(&self) -> usize {
        self.initial_out_of_line_buf_len - self.out_of_line_buf.len()
    }

    /// The number of out-of-line bytes not yet accounted for by a `read_out_of_line`
    /// call.
    pub fn remaining_out_of_line(&self) -> usize {
        self.out_of_line_buf.len()
    }

    /// The number of handles that have not yet been consumed.
    pub fn remaining_handles(&self) -> usize {
        self.handles.len()
    }

    /// Returns a slice of the next `len` bytes to be decoded into and shifts the decoding buffer.
    pub fn next_slice(&mut self, len: usize) -> Result<&[u8]> {
        split_off_front(&mut self.buf, len)
    }

    /// Like `next_slice`, but doesn't remove the bytes from `Self`.
    pub fn peek_slice(&mut self, len: usize) -> Result<&[u8]> {
        self.buf.get(0..len).ok_or_else(|| std::process::abort())
    }

    /// Take the next handle from the `handles` list and shift the list down by one element.
    pub fn take_handle(&mut self) -> Result<Handle> {
        split_off_first_mut(&mut self.handles).map(take_handle)
    }

    /// A convenience method to skip over the specified number of zero bytes used for padding, also
    /// checking that all those bytes are in fact zeroes.
    pub fn skip_padding(&mut self, len: usize) -> Result<()> {
        let padding_start = self.inline_pos();
        let padding = self.next_slice(len)?;
        for i in 0..padding.len() {
            if padding[i] != 0 {
                return Err(Error::NonZeroPadding {
                    padding_start,
                    non_zero_pos: padding_start + i,
                });
            }
        }
        Ok(())
    }

    /// Returns the inline alignment of an object of type `Target` for this decoder.
    pub fn inline_align_of<Target: Decodable>(&self) -> usize {
        Target::inline_align(&self.context)
    }

    /// Returns the inline size of an object of type `Target` for this decoder.
    pub fn inline_size_of<Target: Decodable>(&self) -> usize {
        Target::inline_size(&self.context)
    }

    /// Skips padding at the end of the object, by decoding as many bytes as
    /// necessary to decode `inline_size_of::<Target>()` bytes starting at the
    /// `start_pos`. Uses `Decoder::skip_padding`, so will check that all the
    /// skipped bytes are indeed zeroes.
    pub fn skip_tail_padding<Target: Decodable>(&mut self, start_pos: usize) -> Result<()> {
        debug_assert!(start_pos <= self.inline_pos());
        self.skip_padding(self.inline_size_of::<Target>() - (self.inline_pos() - start_pos))
    }

    /// Returns the decoder's context.
    pub fn context(&self) -> &Context {
        &self.context
    }
}

/// A trait for specifying the inline layout of an encoded object.
pub trait Layout {
    /// Returns the minimum required alignment of the inline portion of the
    /// encoded object.
    fn inline_align(context: &Context) -> usize
    where
        Self: Sized;

    /// Returns the size of the inline portion of the encoded object, including
    /// padding for the type's minimum alignment.
    fn inline_size(context: &Context) -> usize
    where
        Self: Sized;
}

/// An object-safe extension of the `Layout` trait.
///
/// This trait should not be implemented directly. Instead, types should
/// implement `Layout` and rely on the automatic implementation of this one.
///
/// The purpose of this trait is to provide access to inline size and alignment
/// values through `dyn Encodable` trait objects, including generic contexts
/// where they are allowed such as `T: Encodable + ?Sized`.
pub trait LayoutObject: Layout {
    /// See `Layout::inline_align`.
    fn inline_align(&self, context: &Context) -> usize;

    /// See `Layout::inline_size`.
    fn inline_size(&self, context: &Context) -> usize;
}

impl<T: Layout> LayoutObject for T {
    fn inline_align(&self, context: &Context) -> usize {
        <T as Layout>::inline_align(context)
    }

    fn inline_size(&self, context: &Context) -> usize {
        <T as Layout>::inline_size(context)
    }
}

/// A type which can be FIDL2-encoded into a buffer.
///
/// Often an `Encodable` type should also be `Decodable`, but this is not always
/// the case. For example, both `String` and `&str` are encodable, but `&str` is
/// not decodable since it does not own any memory to store the string.
///
/// This trait is object-safe, meaning it is possible to create `dyn Encodable`
/// trait objects. Using them instead of generic `T: Encodable` types can help
/// reduce binary bloat. However, they can only be encoded directly: there are
/// no implementations of `Encodable` for enclosing types such as
/// `Vec<&dyn Encodable>`, and similarly for references, arrays, tuples, etc.
pub trait Encodable: LayoutObject {
    /// Encode the object into the buffer.
    /// Any handles stored in the object are swapped for `Handle::INVALID`.
    /// Calls to this function should ensure that `encoder.offset` is a multiple of `Layout::inline_size`.
    /// Successful calls to this function should increase `encoder.offset` by `Layout::inline_size`.
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()>;
}

/// A type which can be FIDL2-decoded from a buffer.
///
/// This trait is not object-safe, since `new_empty` returns `Self`. This is not
/// really a problem: there are not many use cases for `dyn Decodable`.
pub trait Decodable: Layout {
    /// Creates a new value of this type with an "empty" representation.
    fn new_empty() -> Self;

    /// Decodes an object of this type from the provided buffer and list of handles.
    /// On success, returns `Self`, as well as the yet-unused tails of the data and handle buffers.
    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()>;
}

macro_rules! impl_layout {
    ($ty:ty, align: $align:expr, size: $size:expr) => {
        impl Layout for $ty {
            fn inline_size(_context: &Context) -> usize {
                $size
            }
            fn inline_align(_context: &Context) -> usize {
                $align
            }
        }
    };
}

macro_rules! impl_layout_forall_T {
    ($ty:ty, align: $align:expr, size: $size:expr) => {
        impl<T: Layout> Layout for $ty {
            fn inline_size(_context: &Context) -> usize {
                $size
            }
            fn inline_align(_context: &Context) -> usize {
                $align
            }
        }
    };
}

macro_rules! impl_codable_num { ($($prim_ty:ty => $reader:ident + $writer:ident,)*) => { $(
    impl Layout for $prim_ty {
        fn inline_size(_context: &Context) -> usize { mem::size_of::<$prim_ty>() }
        fn inline_align(_context: &Context) -> usize { mem::size_of::<$prim_ty>() }
    }

    impl Encodable for $prim_ty {
        fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
            let slot = encoder.next_slice(mem::size_of::<Self>())?;
            LittleEndian::$writer(slot, *self);
            Ok(())
        }
    }

    impl Decodable for $prim_ty {
        fn new_empty() -> Self { 0 as $prim_ty }
        fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
            let end = mem::size_of::<Self>();
            let range = split_off_front(&mut decoder.buf, end)?;
            *self = LittleEndian::$reader(range);
            Ok(())
        }
    }
)* } }

impl_codable_num!(
    u16 => read_u16 + write_u16,
    u32 => read_u32 + write_u32,
    u64 => read_u64 + write_u64,
    i16 => read_i16 + write_i16,
    i32 => read_i32 + write_i32,
    i64 => read_i64 + write_i64,
    f32 => read_f32 + write_f32,
    f64 => read_f64 + write_f64,
);

impl_layout!(bool, align: 1, size: 1);

impl Encodable for bool {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        let slot = encoder.next_slice(1)?;
        slot[0] = if *self { 1 } else { 0 };
        Ok(())
    }
}

impl Decodable for bool {
    fn new_empty() -> Self {
        false
    }
    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        let num = *split_off_first(&mut decoder.buf)?;
        *self = match num {
            0 => false,
            1 => true,
            _ => return Err(Error::Invalid),
        };
        Ok(())
    }
}

impl_layout!(u8, align: 1, size: 1);

impl Encodable for u8 {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        let slot = encoder.next_slice(1)?;
        slot[0] = *self;
        Ok(())
    }
}

impl Decodable for u8 {
    fn new_empty() -> Self {
        0
    }
    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        *self = *split_off_first(&mut decoder.buf)?;
        Ok(())
    }
}

impl_layout!(i8, align: 1, size: 1);

impl Encodable for i8 {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        let slot = encoder.next_slice(1)?;
        slot[0] = *self as u8;
        Ok(())
    }
}

impl Decodable for i8 {
    fn new_empty() -> Self {
        0
    }
    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        *self = *split_off_first(&mut decoder.buf)? as i8;
        Ok(())
    }
}

fn encode_array<T: Encodable>(encoder: &mut Encoder<'_>, slice: &mut [T]) -> Result<()> {
    encoder.recurse(|encoder| {
        for item in slice {
            item.encode(encoder)?;
        }
        Ok(())
    })
}

fn decode_array<T: Decodable>(decoder: &mut Decoder<'_>, slice: &mut [T]) -> Result<()> {
    decoder.recurse(|decoder| {
        for item in slice {
            item.decode(decoder)?;
        }
        Ok(())
    })
}

macro_rules! impl_codable_for_fixed_array { ($($len:expr,)*) => { $(
    impl<T: Layout> Layout for [T; $len] {
        fn inline_align(context: &Context) -> usize { T::inline_align(context) }
        fn inline_size(context: &Context) -> usize { T::inline_size(context) * $len }
    }

    impl<T: Encodable> Encodable for [T; $len] {
        fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
            encode_array(encoder, self)
        }
    }

    impl<T: Decodable> Decodable for [T; $len] {
        fn new_empty() -> Self {
            let mut arr = mem::MaybeUninit::<[T; $len]>::uninit();
            unsafe {
                let arr_ptr = arr.as_mut_ptr() as *mut T;
                for i in 0..$len {
                    ptr::write(arr_ptr.offset(i as isize), T::new_empty());
                }
                arr.assume_init()
            }
        }

        fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
            decode_array(decoder, self)
        }
    }
)* } }

// Unfortunately, we cannot be generic over the length of a fixed array
// even though its part of the type (this will hopefully be added in the
// future) so for now we implement encodable for only the first 33 fixed
// size array types.
#[rustfmt::skip]
impl_codable_for_fixed_array!( 0,  1,  2,  3,  4,  5,  6,  7,
                               8,  9, 10, 11, 12, 13, 14, 15,
                              16, 17, 18, 19, 20, 21, 22, 23,
                              24, 25, 26, 27, 28, 29, 30, 31,
                              32,);
// Hack for FIDL library fuchsia.sysmem
impl_codable_for_fixed_array!(64,);
// Hack for FIDL library fuchsia.net
impl_codable_for_fixed_array!(256,);

fn encode_byte_slice(encoder: &mut Encoder<'_>, slice_opt: Option<&[u8]>) -> Result<()> {
    match slice_opt {
        None => encode_absent_vector(encoder),
        Some(slice) => {
            // Two u64: (len, present)
            (slice.len() as u64).encode(encoder)?;
            ALLOC_PRESENT_U64.encode(encoder)?;
            encoder.write_out_of_line(slice.len(), |encoder| {
                let slot = encoder.next_slice(slice.len())?;
                slot.copy_from_slice(slice);
                Ok(())
            })
        }
    }
}

/// Encode an missing vector-like component.
pub fn encode_absent_vector(encoder: &mut Encoder<'_>) -> Result<()> {
    0u64.encode(encoder)?;
    ALLOC_ABSENT_U64.encode(encoder)
}

/// Encode an optional iterator over encodable elements into a FIDL vector-like representation.
pub fn encode_encodable_iter<Iter, T>(
    encoder: &mut Encoder<'_>,
    iter_opt: Option<Iter>,
) -> Result<()>
where
    Iter: ExactSizeIterator<Item = T>,
    T: Encodable,
{
    match iter_opt {
        None => encode_absent_vector(encoder),
        Some(iter) => {
            // Two u64: (len, present)
            (iter.len() as u64).encode(encoder)?;
            ALLOC_PRESENT_U64.encode(encoder)?;
            if iter.len() == 0 {
                return Ok(());
            }
            let bytes_len = iter.len() * encoder.inline_size_of::<T>();
            encoder.write_out_of_line(bytes_len, |encoder| {
                encoder.recurse(|encoder| {
                    for mut item in iter {
                        item.encode(encoder)?;
                    }
                    Ok(())
                })
            })
        }
    }
}

/// Attempts to decode a string into `string`, returning a `bool`
/// indicating whether or not a string was present.
fn decode_string(decoder: &mut Decoder<'_>, string: &mut String) -> Result<bool> {
    let mut len: u64 = 0;
    len.decode(decoder)?;

    let mut present: u64 = 0;
    present.decode(decoder)?;

    match present {
        ALLOC_ABSENT_U64 => {
            return if len == 0 { Ok(false) } else { Err(Error::UnexpectedNullRef) }
        }
        ALLOC_PRESENT_U64 => {}
        _ => return Err(Error::Invalid),
    };
    let len = len as usize;
    decoder.read_out_of_line(len, |decoder| {
        string.truncate(0);
        string.push_str(str::from_utf8(decoder.buf).map_err(|_| Error::Utf8Error)?);
        Ok(true)
    })
}

/// Attempts to decode a vec into `vec`, returning a `bool`
/// indicating whether or not a vec was present.
fn decode_vec<T: Decodable>(decoder: &mut Decoder<'_>, vec: &mut Vec<T>) -> Result<bool> {
    let mut len: u64 = 0;
    len.decode(decoder)?;

    let mut present: u64 = 0;
    present.decode(decoder)?;

    match present {
        ALLOC_ABSENT_U64 => {
            return if len == 0 { Ok(false) } else { Err(Error::UnexpectedNullRef) }
        }
        ALLOC_PRESENT_U64 => {}
        _ => return Err(Error::Invalid),
    }

    let len = len as usize;
    let bytes_len = len * decoder.inline_size_of::<T>();
    decoder.read_out_of_line(bytes_len, |decoder| {
        decoder.recurse(|decoder| {
            vec.truncate(0);
            for _ in 0..len {
                vec.push(T::new_empty());
                // We just pushed an element on, so the `unwrap` will succeed.
                vec.last_mut().unwrap().decode(decoder)?;
            }
            Ok(true)
        })
    })
}

impl_layout!(&str, align: 8, size: 16);

impl Encodable for &str {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        encode_byte_slice(encoder, Some(self.as_bytes()))
    }
}

impl_layout!(String, align: 8, size: 16);

impl Encodable for String {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        encode_byte_slice(encoder, Some(self.as_bytes()))
    }
}

impl Decodable for String {
    fn new_empty() -> Self {
        String::new()
    }

    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        if decode_string(decoder, self)? {
            Ok(())
        } else {
            Err(Error::NotNullable)
        }
    }
}

impl_layout!(Option<&str>, align: 8, size: 16);

impl Encodable for Option<&str> {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        encode_byte_slice(encoder, self.as_ref().map(|x| x.as_bytes()))
    }
}

impl_layout!(Option<String>, align: 8, size: 16);

impl Encodable for Option<String> {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        encode_byte_slice(encoder, self.as_ref().map(|x| x.as_bytes()))
    }
}

impl Decodable for Option<String> {
    fn new_empty() -> Self {
        None
    }

    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        let was_some;
        {
            let string = self.get_or_insert(String::new());
            was_some = decode_string(decoder, string)?;
        }
        if !was_some {
            *self = None
        }
        Ok(())
    }
}

impl_layout_forall_T!(&mut dyn ExactSizeIterator<Item = T>, align: 8, size: 16);

impl<T: Encodable> Encodable for &mut dyn ExactSizeIterator<Item = T> {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        encode_encodable_iter(encoder, Some(self))
    }
}

impl_layout_forall_T!(&mut [T], align: 8, size: 16);

impl<T: Encodable> Encodable for &mut [T] {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        encode_encodable_iter(encoder, Some(self.iter_mut()))
    }
}

impl_layout_forall_T!(Vec<T>, align: 8, size: 16);

impl<T: Encodable> Encodable for Vec<T> {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        encode_encodable_iter(encoder, Some(self.iter_mut()))
    }
}

impl<T: Decodable> Decodable for Vec<T> {
    fn new_empty() -> Self {
        Vec::new()
    }

    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        if decode_vec(decoder, self)? {
            Ok(())
        } else {
            Err(Error::NotNullable)
        }
    }
}

impl_layout_forall_T!(Option<&mut dyn ExactSizeIterator<Item = T>>, align: 8, size: 16);

impl<T: Encodable> Encodable for Option<&mut dyn ExactSizeIterator<Item = T>> {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        encode_encodable_iter(encoder, self.as_mut().map(|x| &mut **x))
    }
}

impl_layout_forall_T!(Option<&mut [T]>, align: 8, size: 16);

impl<T: Encodable> Encodable for Option<&mut [T]> {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        encode_encodable_iter(encoder, self.as_mut().map(|x| x.iter_mut()))
    }
}

impl_layout_forall_T!(Option<Vec<T>>, align: 8, size: 16);

impl<T: Encodable> Encodable for Option<Vec<T>> {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        encode_encodable_iter(encoder, self.as_mut().map(|x| x.iter_mut()))
    }
}

impl<T: Decodable> Decodable for Option<Vec<T>> {
    fn new_empty() -> Self {
        None
    }

    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        let was_some;
        {
            let vec = self.get_or_insert(Vec::new());
            was_some = decode_vec(decoder, vec)?;
        }
        if !was_some {
            *self = None
        }
        Ok(())
    }
}

/// A shorthand macro for calling `Encodable::encode()` on a type
/// without importing the `Encodable` trait.
#[macro_export]
macro_rules! fidl_encode {
    ($val:expr, $encoder:expr) => {
        $crate::encoding::Encodable::encode($val, $encoder)
    };
}

/// A shorthand macro for calling `Decodable::decode()` on a type
/// without importing the `Decodable` trait.
#[macro_export]
macro_rules! fidl_decode {
    ($val:expr, $decoder:expr) => {
        $crate::encoding::Decodable::decode($val, $decoder)
    };
}

/// A shorthand macro for calling `Decodable::new_empty()` on a type
/// without importing the `Decodable` trait.
#[macro_export]
macro_rules! fidl_new_empty {
    ($type:ty) => {
        <$type as $crate::encoding::Decodable>::new_empty()
    };
}

/// Declare a bits type and implement the FIDL coding traits for it.
///
/// Example:
///
/// ```rust
/// fidl_bits!(MyBits (u32) { BAR = 5, BAZ = 6, });
///
/// // expands to:
///
///  bitflags! {
///    struct MyBits: u32 {
///      const BAR = 5;
///      const BAZ = 6;
///    }
///  }
///
///  impl Encodable for MyBits { ... }
///  impl Decodable for MyBits { ... }
/// ```
#[macro_export]
macro_rules! fidl_bits {
    ($name:ident ($prim_ty:ident) { $($key:ident = $value:expr,)* }) => {
        $crate::bitflags! {
            pub struct $name: $prim_ty {
                $(
                    const $key = $value;
                )*
            }
        }

        impl $crate::encoding::Layout for $name {
            fn inline_align(context: &$crate::encoding::Context) -> usize {
                <$prim_ty as $crate::encoding::Layout>::inline_align(context)
            }

            fn inline_size(context: &$crate::encoding::Context) -> usize {
                <$prim_ty as $crate::encoding::Layout>::inline_size(context)
            }
        }

        impl $crate::encoding::Encodable for $name {
            fn encode(&mut self, encoder: &mut $crate::encoding::Encoder<'_>)
                -> ::std::result::Result<(), $crate::Error>
            {
                $crate::fidl_encode!(&mut self.bits, encoder)
            }
        }

        impl $crate::encoding::Decodable for $name {
            fn new_empty() -> Self {
                Self::empty()
            }

            fn decode(&mut self, decoder: &mut $crate::encoding::Decoder<'_>)
                -> ::std::result::Result<(), $crate::Error>
            {
                let mut prim = $crate::fidl_new_empty!($prim_ty);
                $crate::fidl_decode!(&mut prim, decoder)?;
                *self = Self::from_bits(prim).ok_or($crate::Error::Invalid)?;
                Ok(())
            }
        }
    }
}

/// Declare an enum type and implement the FIDL coding traits for it.
///
/// Example:
///
/// ```rust
/// fidl_enum!(MyEnum (u32) { BAR = 5, BAZ = 6, });
///
/// // expands to:
///
///  #[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
///  #[repr($prim_ty)]
///  pub enum MyEnum {
///     BAR = 5,
///     BAZ = 6,
///  }
///
///  impl MyEnum {
///     pub fn from_primitive(prim: u32) -> Option<Self> { ... }
///     pub fn into_primitive(self) -> u32 { ... }
///  }
///
///  impl Encodable for MyEnum { ... }
///  impl Decodable for MyEnum { ... }
/// ```
#[macro_export]
macro_rules! fidl_enum {
    ($name:ident ($prim_ty:ident) { $($key:ident = $value:expr,)* }) => {
        #[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
        #[repr($prim_ty)]
        pub enum $name {
            $(
                $key = $value,
            )*
        }

        impl $name {
            pub fn from_primitive(prim: $prim_ty) -> Option<Self> {
                match prim {
                    $(
                        $value => Some($name::$key),
                    )*
                    _ => None,
                }
            }

            pub fn into_primitive(self) -> $prim_ty {
                self as $prim_ty
            }
        }

        impl $crate::encoding::Layout for $name {
            fn inline_align(context: &$crate::encoding::Context) -> usize {
                <$prim_ty as $crate::encoding::Layout>::inline_align(context)
            }

            fn inline_size(context: &$crate::encoding::Context) -> usize {
                <$prim_ty as $crate::encoding::Layout>::inline_size(context)
            }
        }

        impl $crate::encoding::Encodable for $name {
            fn encode(&mut self, encoder: &mut $crate::encoding::Encoder<'_>)
                -> ::std::result::Result<(), $crate::Error>
            {
                $crate::fidl_encode!(&mut (*self as $prim_ty), encoder)
            }
        }

        impl $crate::encoding::Decodable for $name {
            fn new_empty() -> Self {
                // Returns the first declared variant
                #![allow(unreachable_code)]
                $(
                    return $name::$key;
                )*
                panic!("new_empty called on enum with no variants")
            }

            fn decode(&mut self, decoder: &mut $crate::encoding::Decoder<'_>)
                -> ::std::result::Result<(), $crate::Error>
            {
                let mut prim = $crate::fidl_new_empty!($prim_ty);
                $crate::fidl_decode!(&mut prim, decoder)?;
                *self = Self::from_primitive(prim).ok_or($crate::Error::Invalid)?;
                Ok(())
            }
        }
    }
}

impl_layout!(Handle, align: 4, size: 4);

impl Encodable for Handle {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        ALLOC_PRESENT_U32.encode(encoder)?;
        let handle = take_handle(self);
        encoder.handles.push(handle);
        Ok(())
    }
}

impl Decodable for Handle {
    fn new_empty() -> Self {
        Handle::invalid()
    }
    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        let mut present: u32 = 0;
        present.decode(decoder)?;
        match present {
            ALLOC_ABSENT_U32 => return Err(Error::NotNullable),
            ALLOC_PRESENT_U32 => {}
            _ => return Err(Error::Invalid),
        }
        *self = decoder.take_handle()?;
        Ok(())
    }
}

impl_layout!(Option<Handle>, align: 4, size: 4);

impl Encodable for Option<Handle> {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        match self {
            Some(handle) => handle.encode(encoder),
            None => ALLOC_ABSENT_U32.encode(encoder),
        }
    }
}

impl Decodable for Option<Handle> {
    fn new_empty() -> Self {
        None
    }
    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        let mut present: u32 = 0;
        present.decode(decoder)?;
        match present {
            ALLOC_ABSENT_U32 => {
                *self = None;
                Ok(())
            }
            ALLOC_PRESENT_U32 => {
                *self = Some(decoder.take_handle()?);
                Ok(())
            }
            _ => Err(Error::Invalid),
        }
    }
}

/// A macro for implementing the `Encodable` and `Decodable` traits for a type
/// which implements the `fuchsia_zircon::HandleBased` trait.
// TODO(cramertj) replace when specialization is stable
#[macro_export]
macro_rules! handle_based_codable {
    ($($ty:ident$(:- <$($generic:ident,)*>)*, )*) => { $(
        impl<$($($generic,)*)*> $crate::encoding::Layout for $ty<$($($generic,)*)*> {
            fn inline_align(_context: &$crate::encoding::Context) -> usize { 4 }
            fn inline_size(_context: &$crate::encoding::Context) -> usize { 4 }
        }

        impl<$($($generic,)*)*> $crate::encoding::Encodable for $ty<$($($generic,)*)*> {
            fn encode(&mut self, encoder: &mut $crate::encoding::Encoder<'_>)
                -> $crate::Result<()>
            {
                let mut handle = $crate::encoding::take_handle(self);
                $crate::fidl_encode!(&mut handle, encoder)
            }
        }

        impl<$($($generic,)*)*> $crate::encoding::Decodable for $ty<$($($generic,)*)*> {
            fn new_empty() -> Self {
                <$ty<$($($generic,)*)*> as $crate::handle::HandleBased>::from_handle($crate::handle::Handle::invalid())
            }
            fn decode(&mut self, decoder: &mut $crate::encoding::Decoder<'_>)
                -> $crate::Result<()>
            {
                let mut handle = $crate::handle::Handle::invalid();
                $crate::fidl_decode!(&mut handle, decoder)?;
                *self = <$ty<$($($generic,)*)*> as $crate::handle::HandleBased>::from_handle(handle);
                Ok(())
            }
        }

        impl<$($($generic,)*)*> $crate::encoding::Layout for Option<$ty<$($($generic,)*)*>> {
            fn inline_align(_context: &$crate::encoding::Context) -> usize { 4 }
            fn inline_size(_context: &$crate::encoding::Context) -> usize { 4 }
        }

        impl<$($($generic,)*)*> $crate::encoding::Encodable for Option<$ty<$($($generic,)*)*>> {
            fn encode(&mut self, encoder: &mut $crate::encoding::Encoder<'_>)
                -> $crate::Result<()>
            {
                match self {
                    Some(handle) => $crate::fidl_encode!(handle, encoder),
                    None => $crate::fidl_encode!(&mut $crate::encoding::ALLOC_ABSENT_U32, encoder),
                }
            }
        }

        impl<$($($generic,)*)*> $crate::encoding::Decodable for Option<$ty<$($($generic,)*)*>> {
            fn new_empty() -> Self { None }
            fn decode(&mut self, decoder: &mut $crate::encoding::Decoder<'_>) -> $crate::Result<()> {
                let mut handle: Option<$crate::handle::Handle> = None;
                $crate::fidl_decode!(&mut handle, decoder)?;
                *self = handle.map(Into::into);
                Ok(())
            }
        }
    )* }
}

impl Layout for zx_status::Status {
    fn inline_size(_context: &Context) -> usize {
        mem::size_of::<zx_status::zx_status_t>()
    }
    fn inline_align(_context: &Context) -> usize {
        mem::size_of::<zx_status::zx_status_t>()
    }
}

impl Encodable for zx_status::Status {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        let slot = encoder.next_slice(mem::size_of::<zx_status::zx_status_t>())?;
        LittleEndian::write_i32(slot, self.into_raw());
        Ok(())
    }
}

impl Decodable for zx_status::Status {
    fn new_empty() -> Self {
        Self::from_raw(0)
    }
    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        let end = mem::size_of::<zx_status::zx_status_t>();
        let range = split_off_front(&mut decoder.buf, end)?;
        *self = Self::from_raw(LittleEndian::read_i32(range));
        Ok(())
    }
}

/// The body of a FIDL Epitaph
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct EpitaphBody {
    /// The error status
    pub error: zx_status::Status,
}

impl Layout for EpitaphBody {
    fn inline_align(context: &Context) -> usize {
        <zx_status::Status as Layout>::inline_align(context)
    }
    fn inline_size(context: &Context) -> usize {
        <zx_status::Status as Layout>::inline_size(context)
    }
}

impl Encodable for EpitaphBody {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        self.error.encode(encoder)
    }
}

impl Decodable for EpitaphBody {
    fn new_empty() -> Self {
        Self { error: zx_status::Status::new_empty() }
    }
    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        self.error.decode(decoder)
    }
}

#[cfg(target_os = "fuchsia")]
mod zx_encoding {
    use fuchsia_zircon as zx;

    type ZxChannel = zx::Channel;
    type ZxDebugLog = zx::DebugLog;
    type ZxEvent = zx::Event;
    type ZxEventPair = zx::EventPair;
    type ZxFifo = zx::Fifo;
    type ZxGuest = zx::Guest;
    type ZxInterrupt = zx::Interrupt;
    type ZxJob = zx::Job;
    type ZxProcess = zx::Process;
    type ZxResource = zx::Resource;
    type ZxSocket = zx::Socket;
    type ZxThread = zx::Thread;
    type ZxTimer = zx::Timer;
    type ZxPort = zx::Port;
    type ZxVmar = zx::Vmar;
    type ZxVmo = zx::Vmo;
    handle_based_codable![
        ZxChannel,
        ZxDebugLog,
        ZxEvent,
        ZxEventPair,
        ZxFifo,
        ZxGuest,
        ZxInterrupt,
        ZxJob,
        ZxProcess,
        ZxResource,
        ZxSocket,
        ZxThread,
        ZxTimer,
        ZxPort,
        ZxVmar,
        ZxVmo,
    ];
}

#[cfg(target_os = "fuchsia")]
pub use zx_encoding::*;

#[cfg(not(target_os = "fuchsia"))]
mod fidl_handle_encoding {
    use super::*;

    type FidlChannel = crate::handle::Channel;
    type FidlDebugLog = crate::handle::DebugLog;
    type FidlEvent = crate::handle::Event;
    type FidlEventPair = crate::handle::EventPair;
    type FidlSocket = crate::handle::Socket;
    type FidlVmo = crate::handle::Vmo;

    handle_based_codable![FidlChannel, FidlEvent, FidlEventPair, FidlSocket, FidlVmo,];

    // Stub host serialization of the FidlDebugLog.
    impl_layout!(FidlDebugLog, align: 1, size: 1);

    impl Encodable for FidlDebugLog {
        fn encode(&mut self, _: &mut Encoder<'_>) -> Result<()> {
            Err(Error::InvalidHostHandle)
        }
    }

    impl Decodable for FidlDebugLog {
        fn new_empty() -> Self {
            FidlDebugLog::from(Handle::invalid())
        }

        fn decode(&mut self, _: &mut Decoder<'_>) -> Result<()> {
            Err(Error::InvalidHostHandle)
        }
    }
}

#[cfg(not(target_os = "fuchsia"))]
pub use fidl_handle_encoding::*;

/// A trait that provides automatic support for nullable types.
///
/// Types that implement this trait will automatically receive `Encodable` and
/// `Decodable` implementations for `Option<Box<Self>>` (nullable owned type),
/// and `Encodable` for `Option<&mut Self>` (nullable borrowed type).
pub trait Autonull: Encodable + Decodable {
    /// Returns true if the type is naturally able to be nullable.
    ///
    /// Types that return true (e.g., xunions) encode `Some(x)` the same as `x`,
    /// and `None` as a full bout of inline zeros. Types that return false
    /// (e.g., structs) encode `Some(x)` as `ALLOC_PRESENT_U64` with an
    /// out-of-line payload, and `None` as `ALLOC_ABSENT_U64`.
    fn naturally_nullable(context: &Context) -> bool;
}

impl<T: Autonull> Layout for Option<&mut T> {
    fn inline_align(context: &Context) -> usize {
        if T::naturally_nullable(context) {
            <T as Layout>::inline_align(context)
        } else {
            8
        }
    }
    fn inline_size(context: &Context) -> usize {
        if T::naturally_nullable(context) {
            <T as Layout>::inline_size(context)
        } else {
            8
        }
    }
}

impl<T: Autonull> Encodable for Option<&mut T> {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        if T::naturally_nullable(&encoder.context) {
            match self {
                Some(x) => x.encode(encoder),
                None => {
                    for byte in encoder.next_slice(encoder.inline_size_of::<T>())? {
                        *byte = 0;
                    }
                    Ok(())
                }
            }
        } else {
            match self {
                Some(x) => {
                    ALLOC_PRESENT_U64.encode(encoder)?;
                    encoder.write_out_of_line(encoder.inline_size_of::<T>(), |encoder| {
                        x.encode(encoder)
                    })
                }
                None => ALLOC_ABSENT_U64.encode(encoder),
            }
        }
    }
}

impl<T: Autonull> Layout for Option<Box<T>> {
    fn inline_align(context: &Context) -> usize {
        <Option<&mut T> as Layout>::inline_align(context)
    }
    fn inline_size(context: &Context) -> usize {
        <Option<&mut T> as Layout>::inline_size(context)
    }
}

impl<T: Autonull> Encodable for Option<Box<T>> {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        self.as_deref_mut().encode(encoder)
    }
}

// Presence indicators always include at least one non-zero byte,
// while absence indicators should always be entirely zeros.
fn check_for_presence(decoder: &mut Decoder<'_>, inline_size: usize) -> Result<bool> {
    Ok(decoder.peek_slice(inline_size)?.iter().any(|byte| *byte != 0))
}

impl<T: Autonull> Decodable for Option<Box<T>> {
    fn new_empty() -> Self {
        None
    }
    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        if T::naturally_nullable(&decoder.context) {
            let inline_size = decoder.inline_size_of::<T>();
            let present = check_for_presence(decoder, inline_size)?;
            if present {
                self.get_or_insert_with(|| Box::new(T::new_empty())).decode(decoder)
            } else {
                *self = None;
                // Eat the full `inline_size` bytes including the
                // ALLOC_ABSENT that we only peeked at before
                decoder.skip_padding(inline_size)?;
                Ok(())
            }
        } else {
            let mut present: u64 = 0;
            present.decode(decoder)?;
            match present {
                ALLOC_PRESENT_U64 => decoder
                    .read_out_of_line(decoder.inline_size_of::<T>(), |decoder| {
                        self.get_or_insert_with(|| Box::new(T::new_empty())).decode(decoder)
                    }),
                ALLOC_ABSENT_U64 => {
                    *self = None;
                    Ok(())
                }
                _ => Err(Error::Invalid),
            }
        }
    }
}

/// A macro which implements the FIDL `Encodable` and `Decodable` traits
/// for an existing struct.
#[macro_export]
macro_rules! fidl_struct {
    (
        name: $name:ty,
        members: [$(
            $member_name:ident {
                ty: $member_ty:ty,
                offset_v1: $member_offset_v1:expr,
            },
        )*],
        size_v1: $size_v1:expr,
        align_v1: $align_v1:expr,
    ) => {
        impl $crate::encoding::Layout for $name {
            fn inline_align(_context: &$crate::encoding::Context) -> usize {
                $align_v1
            }

            fn inline_size(_context: &$crate::encoding::Context) -> usize {
                $size_v1
            }
        }

        impl $crate::encoding::Encodable for $name {
            fn encode(&mut self, encoder: &mut $crate::encoding::Encoder<'_>) -> $crate::Result<()> {
                encoder.recurse(|encoder| {
                    let mut cur_offset = 0;
                    $(
                        // Skip to the start of the next field
                        let member_offset = $member_offset_v1;
                        encoder.padding(member_offset - cur_offset)?;
                        cur_offset = member_offset;
                        $crate::fidl_encode!(&mut self.$member_name, encoder)?;
                        cur_offset += encoder.inline_size_of::<$member_ty>();
                    )*
                    // Skip to the end of the struct's size
                    encoder.padding(encoder.inline_size_of::<Self>() - cur_offset)?;
                    Ok(())
                })
            }
        }

        impl $crate::encoding::Decodable for $name {
            fn new_empty() -> Self {
                Self {
                    $(
                        $member_name: $crate::fidl_new_empty!($member_ty),
                    )*
                }
            }

            fn decode(&mut self, decoder: &mut $crate::encoding::Decoder<'_>) -> $crate::Result<()> {
                decoder.recurse(|decoder| {
                    let mut cur_offset = 0;
                    $(
                        // Skip to the start of the next field
                        let member_offset = $member_offset_v1;
                        decoder.skip_padding(member_offset - cur_offset)?;
                        cur_offset = member_offset;
                        $crate::fidl_decode!(&mut self.$member_name, decoder)?;
                        cur_offset += decoder.inline_size_of::<$member_ty>();
                    )*
                    // Skip to the end of the struct's size
                    decoder.skip_padding(decoder.inline_size_of::<Self>() - cur_offset)?;
                    Ok(())
                })
            }
        }

        impl $crate::encoding::Autonull for $name {
            fn naturally_nullable(_context: &$crate::encoding::Context) -> bool {
                false
            }
        }
    }
}

/// A macro which creates an empty struct and implements the FIDL `Encodable` and `Decodable`
/// traits for it.
#[macro_export]
macro_rules! fidl_empty_struct {
    ($(#[$attrs:meta])* $name:ident) => {
        $(#[$attrs])*
        #[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
        pub struct $name;

        impl $crate::encoding::Layout for $name {
          fn inline_align(_context: &$crate::encoding::Context) -> usize { 1 }
          fn inline_size(_context: &$crate::encoding::Context) -> usize { 1 }
        }

        impl $crate::encoding::Encodable for $name {
          fn encode(&mut self, encoder: &mut $crate::encoding::Encoder<'_>) -> $crate::Result<()> {
              $crate::fidl_encode!(&mut 0u8, encoder)
          }
        }

        impl $crate::encoding::Decodable for $name {
          fn new_empty() -> Self { $name }
          fn decode(&mut self, decoder: &mut $crate::encoding::Decoder<'_>) -> $crate::Result<()> {
            let mut x = 0u8;
             $crate::fidl_decode!(&mut x, decoder)?;
            if x == 0 {
                 Ok(())
            } else {
                 Err($crate::Error::Invalid)
            }
          }
        }

        impl $crate::encoding::Autonull for $name {
            fn naturally_nullable(_context: &$crate::encoding::Context) -> bool {
                false
            }
        }
    }
}

/// Encode the provided value behind a FIDL "envelope".
pub fn encode_in_envelope(
    val: &mut Option<&mut dyn Encodable>,
    encoder: &mut Encoder<'_>,
) -> Result<()> {
    // u32 num_bytes
    // u32 num_handles
    // 64-bit presence indicator

    // Record the offset of the number of bytes handles in the envelope,
    // so that we can come back to it after writing the bytes and handles
    // (until which point we don't know how many handles will be written).
    let envelope_offset = encoder.offset;
    0u32.encode(encoder)?; // num_bytes
    0u32.encode(encoder)?; // num_handles

    match val {
        Some(x) => {
            ALLOC_PRESENT_U64.encode(encoder)?;
            let bytes_before = encoder.buf.len();
            let handles_before = encoder.handles.len();
            encoder.write_out_of_line(x.inline_size(&encoder.context), |e| x.encode(e))?;
            let mut bytes_written = (encoder.buf.len() - bytes_before) as u32;
            let mut handles_written = (encoder.handles.len() - handles_before) as u32;
            // Back up and overwrite the `0s` for num_bytes and num_handles
            let after_offset = encoder.offset;
            encoder.offset = envelope_offset;
            bytes_written.encode(encoder)?;
            handles_written.encode(encoder)?;
            encoder.offset = after_offset;
        }
        None => ALLOC_ABSENT_U64.encode(encoder)?,
    }
    Ok(())
}

/// Decodes a reserved field in a table (an empty envelope).
pub fn decode_reserved_table_field(decoder: &mut Decoder<'_>) -> Result<()> {
    let mut num_bytes: u32 = 0;
    num_bytes.decode(decoder)?;
    let mut num_handles: u32 = 0;
    num_handles.decode(decoder)?;
    let mut present: u64 = 0;
    present.decode(decoder)?;

    if num_bytes != 0 || num_handles != 0 || present != ALLOC_ABSENT_U64 {
        return Err(Error::UnknownTableField);
    }
    Ok(())
}

/// A macro which implements the table empty constructor and the FIDL `Encodable` and `Decodable`
/// traits for an existing struct whose fields are all `Option`s and may or may not appear in the
/// wire-format representation.
#[macro_export]
macro_rules! fidl_table {
    (
        name: $name:ty,
        members: {$(
            // NOTE: members must be in order from lowest to highest ordinal
            $member_name:ident {
                ty: $member_ty:ty,
                ordinal: $ordinal:expr,
            },
        )*},
    ) => {
        impl $name {
            /// Generates an empty table, with every field set to `None`.
            pub fn empty() -> Self {
                Self {$(
                        $member_name: None,
                )*}
            }
        }

        impl $crate::encoding::Layout for $name {
            fn inline_align(_context: &$crate::encoding::Context) -> usize { 8 }
            fn inline_size(_context: &$crate::encoding::Context) -> usize { 16 }
        }

        impl $crate::encoding::Encodable for $name {
            fn encode(&mut self, encoder: &mut $crate::encoding::Encoder<'_>) -> $crate::Result<()> {
                let members: &mut [(u64, Option<&mut dyn $crate::encoding::Encodable>)] = &mut [$(
                    ($ordinal, self.$member_name.as_mut().map(|x| x as &mut dyn $crate::encoding::Encodable)),
                )*];

                // Cut off the `None` elements at the tail of the table
                let last_some_index = members.iter().rposition(|x| x.1.is_some());

                let members = if let Some(i) = last_some_index {
                    &mut members[..(i + 1)]
                } else {
                    &mut []
                };

                // Vector header
                let max_ordinal = members.last().map(|v| v.0).unwrap_or(0);
                (max_ordinal as u64).encode(encoder)?;
                $crate::encoding::ALLOC_PRESENT_U64.encode(encoder)?;
                let bytes_len = (max_ordinal as usize) * 16; // 16 = ENVELOPE_INLINE_SIZE
                encoder.write_out_of_line(bytes_len, |encoder| {
                    encoder.recurse(|encoder| {
                        let mut next_ordinal_to_write = 1;
                        for (ordinal, encodable) in members.iter_mut() {
                            let ordinal = *ordinal;
                            if ordinal < next_ordinal_to_write || ordinal > max_ordinal {
                                panic!("ordinals out of order in fidl_table! declaration");
                            }
                            while ordinal > next_ordinal_to_write {
                                // Fill in envelopes for missing ordinals.
                                $crate::encoding::encode_in_envelope(&mut None, encoder)?;
                                next_ordinal_to_write += 1;
                            }
                            $crate::encoding::encode_in_envelope(encodable, encoder)?;
                            next_ordinal_to_write += 1;
                        }
                        Ok(())
                    })
                })
            }
        }

        impl $crate::encoding::Decodable for $name {
            fn new_empty() -> Self {
                Self::empty()
            }
            fn decode(&mut self, decoder: &mut $crate::encoding::Decoder<'_>) -> $crate::Result<()> {
                // Decode envelope vector header
                let mut len: u64 = 0;
                $crate::fidl_decode!(&mut len, decoder)?;

                let mut present: u64 = 0;
                $crate::fidl_decode!(&mut present, decoder)?;

                if present != $crate::encoding::ALLOC_PRESENT_U64 {
                    return Err($crate::Error::Invalid);
                }

                let len = len as usize;
                let bytes_len = len * 16; // envelope inline_size is 16
                decoder.read_out_of_line(bytes_len, |decoder| {
                    // Decode the envelope for each type.
                    // u32 num_bytes
                    // u32_num_handles
                    // 64-bit presence indicator
                    let mut _next_ordinal_to_read = 0;
                    $(
                        _next_ordinal_to_read += 1;
                        if decoder.is_empty() {
                            // The remaining fields have been omitted, so set them to None
                            self.$member_name = None;
                        } else {
                            // Decode empty envelopes for gaps in ordinals.
                            while _next_ordinal_to_read < $ordinal {
                                $crate::encoding::decode_reserved_table_field(decoder)?;
                                _next_ordinal_to_read += 1;
                            }
                            let mut num_bytes: u32 = 0;
                            $crate::fidl_decode!(&mut num_bytes, decoder)?;
                            let mut num_handles: u32 = 0;
                            $crate::fidl_decode!(&mut num_handles, decoder)?;
                            let mut present: u64 = 0;
                            $crate::fidl_decode!(&mut present, decoder)?;
                            let bytes_before = decoder.remaining_out_of_line();
                            let handles_before = decoder.remaining_handles();
                            match present {
                                $crate::encoding::ALLOC_PRESENT_U64 => {
                                    decoder.read_out_of_line(
                                        decoder.inline_size_of::<$member_ty>(),
                                        |d| {
                                            let val_ref =
                                               self.$member_name.get_or_insert_with(
                                                    || $crate::fidl_new_empty!($member_ty));
                                            $crate::fidl_decode!(val_ref, d)?;
                                            Ok(())
                                        },
                                    )?;
                                }
                                $crate::encoding::ALLOC_ABSENT_U64 => {
                                    if num_bytes != 0 {
                                        return Err($crate::Error::UnexpectedNullRef);
                                    }
                                    self.$member_name = None;
                                }
                                _ => return Err($crate::Error::Invalid),
                            }
                            if bytes_before != (decoder.remaining_out_of_line() + (num_bytes as usize)) {
                                return Err($crate::Error::Invalid);
                            }
                            if handles_before != (decoder.remaining_handles() + (num_handles as usize)) {
                                return Err($crate::Error::Invalid);
                            }
                        }
                    )*

                    // If there are any remaining non-empty envelopes,
                    // we error since the ordinal is unknown to these bindings.
                    //
                    // NOTE: this is the behavior discussed in previous FIDL
                    // team meetings and is consistent with the behavior on new
                    // extensible union variants and new interface methods.
                    // However, it means that receivers of tables must update
                    // to new generated bindings before they can receive
                    // messages containing new table fields.
                    while !decoder.is_empty() {
                        $crate::encoding::decode_reserved_table_field(decoder)?;
                    }

                    Ok(())
                })
            }
        }
    }
}

/// Decodes the inline portion of a xunion. Returns (ordinal, num_bytes, num_handles).
pub fn decode_xunion_inline_portion(decoder: &mut Decoder) -> Result<(u64, u32, u32)> {
    let mut ordinal: u64 = 0;
    ordinal.decode(decoder)?;

    let mut num_bytes: u32 = 0;
    num_bytes.decode(decoder)?;

    let mut num_handles: u32 = 0;
    num_handles.decode(decoder)?;

    let mut present: u64 = 0;
    present.decode(decoder)?;
    if present != ALLOC_PRESENT_U64 {
        return Err(Error::Invalid);
    }

    Ok((ordinal, num_bytes, num_handles))
}

impl<O, E> Layout for std::result::Result<O, E>
where
    O: Layout,
    E: Layout,
{
    fn inline_align(_context: &Context) -> usize {
        8
    }
    fn inline_size(_context: &Context) -> usize {
        24
    }
}

impl<O, E> Encodable for std::result::Result<O, E>
where
    O: Encodable,
    E: Encodable,
{
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        match self {
            Ok(val) => {
                // Encode success ordinal
                1u64.encode(encoder)?;
                encoder.recurse(|encoder|
                    // If the inline size is 0, meaning the type is (),
                    // encode a zero byte instead because () in this context
                    // means an empty struct, not an absent payload.
                    if encoder.inline_size_of::<O>() == 0 {
                        encode_in_envelope(&mut Some(&mut 0u8), encoder)
                    } else {
                        encode_in_envelope(&mut Some(val), encoder)
                    }
                )
            }
            Err(val) => {
                // Encode error ordinal
                2u64.encode(encoder)?;
                encoder.recurse(|encoder| encode_in_envelope(&mut Some(val), encoder))
            }
        }
    }
}

impl<O, E> Decodable for std::result::Result<O, E>
where
    O: Decodable,
    E: Decodable,
{
    fn new_empty() -> Self {
        Ok(<O as Decodable>::new_empty())
    }

    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        let (ordinal, _, _) = decode_xunion_inline_portion(decoder)?;
        let member_inline_size = match ordinal {
            1 => {
                // If the inline size is 0, meaning the type is (), use an inline
                // size of 1 instead because () in this context means an empty
                // struct, not an absent payload.
                cmp::max(1, decoder.inline_size_of::<O>())
            }
            2 => decoder.inline_size_of::<E>(),
            _ => return Err(Error::UnknownUnionTag),
        };
        decoder.read_out_of_line(member_inline_size, |decoder| {
            decoder.recurse(|decoder| {
                match ordinal {
                    1 => {
                        if let Ok(_) = self {
                            // Do nothing, read the value into the object
                        } else {
                            // Initialize `self` to the right variant
                            *self = Ok(fidl_new_empty!(O));
                        }
                        if let Ok(val) = self {
                            val.decode(decoder)
                        } else {
                            unreachable!()
                        }
                    }
                    2 => {
                        if let Err(_) = self {
                            // Do nothing, read the value into the object
                        } else {
                            // Initialize `self` to the right variant
                            *self = Err(fidl_new_empty!(E));
                        }
                        if let Err(val) = self {
                            val.decode(decoder)
                        } else {
                            unreachable!()
                        }
                    }
                    // Should be unreachable, since we already checked above.
                    ordinal => panic!("unexpected ordinal {:?}", ordinal),
                }
            })
        })
    }
}

/// A macro which declares a new FIDL xunion as a Rust enum and implements the
/// FIDL encoding and decoding traits for it.
#[macro_export]
macro_rules! fidl_xunion {
    (
        $(#[$attrs:meta])*
        name: $name:ident,
        members: [$(
            $(#[$member_docs:meta])*
            $member_name:ident {
                ty: $member_ty:ty,
                // ordinal is the field used when encoding the xunion, and the
                // actual value associated with each variant (i.e. returned by
                // .ordinal()). It will always be one of explicit_ordinal or
                // hashed_ordinal
                ordinal: $member_ordinal:expr,
                // explicit_ordinal and hashed_ordinal are the two sets of
                // ordinals that are checked when decoding xunions. They may
                // both be the same value (explicit) for cases where we we know
                // only one set needs to be supported (e.g. static unions that
                // were migrated over to xunions have used explicit ordinals
                // from the start).
                explicit_ordinal: $explicit_member_ordinal:expr,
                hashed_ordinal: $hashed_member_ordinal:expr,
            },
        )*],
        // Flexible xunions only: name of the unknown variant.
        $( unknown_member: $unknown_name:ident, )?
    ) => {
        $( #[$attrs] )*
        pub enum $name {
            $(
                $(#[$member_docs])*
                $member_name ( $member_ty ),
            )*
            $(
                #[doc(hidden)]
                $unknown_name {
                    ordinal: u64,
                    bytes: Vec<u8>,
                    handles: Vec<$crate::handle::Handle>,
                },
            )?
        }

        impl $name {
            fn ordinal(&self) -> u64 {
                match *self {
                    $(
                        $name::$member_name(_) => $member_ordinal,
                    )*
                    $(
                        $name::$unknown_name { ordinal, .. } => ordinal,
                    )?
                }
            }
        }

        impl $crate::encoding::Layout for $name {
            fn inline_align(_context: &$crate::encoding::Context) -> usize { 8 }
            fn inline_size(_context: &$crate::encoding::Context) -> usize { 24 }
        }

        impl $crate::encoding::Encodable for $name {
            fn encode(&mut self, encoder: &mut $crate::encoding::Encoder<'_>) -> $crate::Result<()> {
                let mut ordinal = self.ordinal();
                // Encode ordinal
                $crate::fidl_encode!(&mut ordinal, encoder)?;
                encoder.recurse(|encoder| {
                    match self {
                        $(
                            $name::$member_name ( val ) => $crate::encoding::encode_in_envelope(&mut Some(val), encoder),
                        )*
                        $(
                            $name::$unknown_name { ordinal: _, bytes, handles } => {
                                // Throw the raw data from the unrecognized variant
                                // back onto the wire. This will allow correct proxies even in
                                // the event that they don't yet recognize this union variant.
                                $crate::fidl_encode!(&mut (bytes.len() as u32), encoder)?;
                                $crate::fidl_encode!(&mut (handles.len() as u32), encoder)?;
                                $crate::fidl_encode!(
                                    &mut $crate::encoding::ALLOC_PRESENT_U64, encoder
                                )?;
                                encoder.append_bytes(bytes);
                                encoder.append_handles(handles);
                                Ok(())
                            },
                        )?
                    }
                })
            }
        }

        impl $crate::encoding::Decodable for $name {
            fn new_empty() -> Self {
                #![allow(unreachable_code)]
                $(
                    return $name::$member_name($crate::fidl_new_empty!($member_ty));
                )*
                $(
                    $name::$unknown_name { ordinal: 0, bytes: vec![], handles: vec![] }
                )?
            }

            fn decode(&mut self, decoder: &mut $crate::encoding::Decoder<'_>) -> $crate::Result<()> {
                #![allow(irrefutable_let_patterns, unused)]
                let (ordinal, num_bytes, num_handles) = $crate::encoding::decode_xunion_inline_portion(decoder)?;
                let member_inline_size = match ordinal {
                    $(
                        $hashed_member_ordinal | $explicit_member_ordinal =>
                            decoder.inline_size_of::<$member_ty>(),
                    )*
                    $(
                        _ => {
                            // We need the expansion to refer to $unknown_name,
                            // so just create and discard an unknown variant.
                            $name::$unknown_name { ordinal: 0, bytes: vec![], handles: vec![] };
                            // Flexible xunion: unknown payloads are considered
                            // a wholly-inline string of bytes.
                            num_bytes as usize
                        }
                    )?
                    // Strict xunion: reject unknown ordinals.
                    _ => return Err($crate::Error::UnknownUnionTag),
                };

                decoder.read_out_of_line(member_inline_size, |decoder| {
                    decoder.recurse(|decoder| {
                        match ordinal {
                            $(
                                $hashed_member_ordinal | $explicit_member_ordinal => {
                                    if let $name::$member_name(_) = self {
                                        // Do nothing, read the value into the object
                                    } else {
                                        // Initialize `self` to the right variant
                                        *self = $name::$member_name(
                                            $crate::fidl_new_empty!($member_ty)
                                        );
                                    }
                                    if let $name::$member_name(val) = self {
                                        $crate::fidl_decode!(val, decoder)?;
                                    } else {
                                        unreachable!()
                                    }
                                }
                            )*
                            $(
                                ordinal => {
                                    let bytes = decoder.next_slice(num_bytes as usize)?.to_vec();
                                    let mut handles = Vec::with_capacity(num_handles as usize);
                                    for _ in 0..num_handles {
                                        handles.push(decoder.take_handle()?);
                                    }
                                    *self = $name::$unknown_name { ordinal, bytes, handles };
                                }
                            )?
                            // This should be unreachable, since we already
                            // checked for unknown ordinals above and returned
                            // an error in the strict case.
                            ordinal => panic!("unexpected ordinal {:?}", ordinal)
                        }
                        Ok(())
                    })
                })
            }
        }

        impl $crate::encoding::Autonull for $name {
            fn naturally_nullable(_context: &$crate::encoding::Context) -> bool {
                true
            }
        }
    }
}

/// Header for transactional FIDL messages
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct TransactionHeader {
    /// Transaction ID which identifies a request-response pair
    tx_id: u32,
    /// Flags set for this message. MUST NOT be validated by bindings
    flags: [u8; 3],
    /// Magic number indicating the message's wire format. Two sides with
    /// different magic numbers are incompatible with each other.
    magic_number: u8,
    /// Ordinal which identifies the FIDL method
    ordinal: u64,
}

impl TransactionHeader {
    /// Returns whether the message containing this TransactionHeader is in a
    /// compatible wire format
    pub fn is_compatible(&self) -> bool {
        self.magic_number == MAGIC_NUMBER_INITIAL
    }
}

fidl_struct! {
    name: TransactionHeader,
    members: [
        tx_id {
            ty: u32,
            offset_v1: 0,
        },
        flags {
            ty: [u8; 3],
            offset_v1: 4,
        },
        magic_number {
            ty: u8,
            offset_v1: 7,
        },
        ordinal {
            ty: u64,
            offset_v1: 8,
        },
    ],
    size_v1: 16,
    align_v1: 8,
}

bitflags! {
    /// Bitflags type for transaction header flags.
    pub struct HeaderFlags: u32 {
        /// Indicates that unions in the transaction message body are encoded
        /// using the xunion format.
        const UNIONS_USE_XUNION_FORMAT = 1 << 0;
    }
}

impl Into<[u8; 3]> for HeaderFlags {
    fn into(self) -> [u8; 3] {
        let mut bytes: [u8; 3] = [0; 3];
        LittleEndian::write_u24(&mut bytes, self.bits);
        bytes
    }
}

impl TransactionHeader {
    /// Creates a new transaction header with the default encode context and magic number.
    pub fn new(tx_id: u32, ordinal: u64) -> Self {
        TransactionHeader::new_full(tx_id, ordinal, &default_encode_context(), MAGIC_NUMBER_INITIAL)
    }
    /// Creates a new transaction header with a specific context and magic number.
    pub fn new_full(tx_id: u32, ordinal: u64, context: &Context, magic_number: u8) -> Self {
        TransactionHeader { tx_id, flags: context.header_flags().into(), magic_number, ordinal }
    }
    /// Returns the header's transaction id.
    pub fn tx_id(&self) -> u32 {
        self.tx_id
    }
    /// Returns the header's message ordinal.
    pub fn ordinal(&self) -> u64 {
        self.ordinal
    }
    /// Returns true if the header is for an epitaph message.
    pub fn is_epitaph(&self) -> bool {
        self.ordinal == EPITAPH_ORDINAL
    }

    /// Returns the magic number.
    pub fn magic_number(&self) -> u8 {
        self.magic_number
    }

    /// Returns the header's flags as a `HeaderFlags` value.
    pub fn flags(&self) -> HeaderFlags {
        HeaderFlags::from_bits_truncate(LittleEndian::read_u24(&self.flags))
    }

    /// Returns the context to use for decoding the message body associated with this header.
    pub fn decoding_context(&self) -> Context {
        Context {}
    }
}

/// Transactional FIDL message
pub struct TransactionMessage<'a, T> {
    /// Header of the message
    pub header: TransactionHeader,
    /// Body of the message
    pub body: &'a mut T,
}

impl<T: Layout> Layout for TransactionMessage<'_, T> {
    fn inline_align(_context: &Context) -> usize {
        0
    }
    fn inline_size(context: &Context) -> usize {
        <TransactionHeader as Layout>::inline_size(context) + T::inline_size(context)
    }
}

impl<T: Encodable> Encodable for TransactionMessage<'_, T> {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        self.header.encode(encoder)?;
        (*self.body).encode(encoder)?;
        Ok(())
    }
}

impl<T: Decodable> Decodable for TransactionMessage<'_, T> {
    fn new_empty() -> Self {
        panic!("cannot create an empty transaction message")
    }
    fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
        self.header.decode(decoder)?;
        decoder.context = self.header.decoding_context();
        (*self.body).decode(decoder)?;
        Ok(())
    }
}

/// Decodes the transaction header from a message.
/// Returns the header and a reference to the tail of the message.
pub fn decode_transaction_header(bytes: &[u8]) -> Result<(TransactionHeader, &[u8])> {
    let mut header = TransactionHeader::new_empty();
    // The header doesn't contain unions, so the context flag doesn't matter.
    let context = Context {};
    let header_len = <TransactionHeader as Layout>::inline_size(&context);
    if bytes.len() < header_len {
        return Err(Error::OutOfRange);
    }
    let (header_bytes, body_bytes) = bytes.split_at(header_len);
    let handles = &mut [];
    Decoder::decode_with_context(&context, header_bytes, handles, &mut header)?;
    Ok((header, body_bytes))
}

// Implementations of Encodable for (&mut Head, ...Tail) and Decodable for (Head, ...Tail)
macro_rules! tuple_impls {
    () => {};

    (($idx:tt => $typ:ident), $( ($nidx:tt => $ntyp:ident), )*) => {
        /*
         * Invoke recursive reversal of list that ends in the macro expansion implementation
         * of the reversed list
        */
        tuple_impls!([($idx, $typ);] $( ($nidx => $ntyp), )*);
        tuple_impls!($( ($nidx => $ntyp), )*); // invoke macro on tail
    };

    /*
     * ([accumulatedList], listToReverse); recursively calls tuple_impls until the list to reverse
     + is empty (see next pattern)
    */
    ([$(($accIdx:tt, $accTyp:ident);)+]
        ($idx:tt => $typ:ident), $( ($nidx:tt => $ntyp:ident), )*) => {
      tuple_impls!([($idx, $typ); $(($accIdx, $accTyp); )*] $( ($nidx => $ntyp), ) *);
    };

    // Finally expand into the implementation
    ([($idx:tt, $typ:ident); $( ($nidx:tt, $ntyp:ident); )*]) => {
        impl<$typ, $( $ntyp ),*> Layout for ($typ, $( $ntyp, )*)
            where $typ: Layout,
                  $( $ntyp: Layout, )*
        {
            fn inline_align(context: &Context) -> usize {
                let mut max = 0;
                if max < $typ::inline_align(context) {
                    max = $typ::inline_align(context);
                }
                $(
                    if max < $ntyp::inline_align(context) {
                        max = $ntyp::inline_align(context);
                    }
                )*
                max
            }

            fn inline_size(context: &Context) -> usize {
                let mut offset = 0;
                offset += $typ::inline_size(context);
                $(
                    offset = round_up_to_align(offset, $ntyp::inline_align(context));
                    offset += $ntyp::inline_size(context);
                )*
                offset
            }
        }

        impl<$typ, $( $ntyp ,)*> Encodable for ($typ, $( $ntyp ,)*)
            where $typ: Encodable,
                  $( $ntyp: Encodable,)*
        {
            fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
                encoder.recurse(|encoder| {
                    let mut cur_offset = 0;
                    self.$idx.encode(encoder)?;
                    cur_offset += encoder.inline_size_of::<$typ>();
                    $(
                        // Skip to the start of the next field
                        let member_offset =
                            round_up_to_align(cur_offset, encoder.inline_align_of::<$ntyp>());
                        encoder.padding(member_offset - cur_offset)?;
                        cur_offset = member_offset;
                        self.$nidx.encode(encoder)?;
                        cur_offset += encoder.inline_size_of::<$ntyp>();
                    )*
                    // Skip to the end of the struct's size
                    encoder.padding(encoder.inline_size_of::<Self>() - cur_offset)?;
                    Ok(())
                })
            }
        }

        impl<$typ, $( $ntyp ),*> Decodable for ($typ, $( $ntyp, )*)
            where $typ: Decodable,
                  $( $ntyp: Decodable, )*
        {
            fn new_empty() -> Self {
                (
                    $typ::new_empty(),
                    $(
                        $ntyp::new_empty(),
                    )*
                )
            }

            fn decode(&mut self, decoder: &mut Decoder<'_>) -> Result<()> {
                decoder.recurse(|decoder| {
                    let mut cur_offset = 0;
                    self.$idx.decode(decoder)?;
                    cur_offset += decoder.inline_size_of::<$typ>();
                    $(
                        // Skip to the start of the next field
                        let member_offset =
                            round_up_to_align(cur_offset, decoder.inline_align_of::<$ntyp>());
                        decoder.skip_padding(member_offset - cur_offset)?;
                        cur_offset = member_offset;
                        self.$nidx.decode(decoder)?;
                        cur_offset += decoder.inline_size_of::<$ntyp>();
                    )*
                    // Skip to the end of the struct's size
                    decoder.skip_padding(decoder.inline_size_of::<Self>() - cur_offset)?;
                    Ok(())
                })
            }
        }
    }
}

tuple_impls!(
    (10 => K),
    (9 => J),
    (8 => I),
    (7 => H),
    (6 => G),
    (5 => F),
    (4 => E),
    (3 => D),
    (2 => C),
    (1 => B),
    (0 => A),
);

// The unit type has 0 size because it represents the absent payload after the
// transaction header in the reponse of a two-way FIDL method such as this one:
//
//     Method() -> ();
//
// However, the unit type is also used in the following situation:
//
//    MethodWithError() -> () error int32;
//
// In this case the response type is std::result::Result<(), i32>, but the ()
// represents an empty struct, which has size 1. To accommodate this, the encode
// and decode methods on std::result::Result handle the () case specially.
impl_layout!((), align: 0, size: 0);

impl Encodable for () {
    fn encode(&mut self, _: &mut Encoder<'_>) -> Result<()> {
        Ok(())
    }
}

impl Decodable for () {
    fn new_empty() -> Self {
        ()
    }
    fn decode(&mut self, _: &mut Decoder<'_>) -> Result<()> {
        Ok(())
    }
}

impl<T: Layout> Layout for &mut T {
    fn inline_align(context: &Context) -> usize {
        T::inline_align(context)
    }
    fn inline_size(context: &Context) -> usize {
        T::inline_size(context)
    }
}

impl<T: Encodable> Encodable for &mut T {
    fn encode(&mut self, encoder: &mut Encoder<'_>) -> Result<()> {
        (&mut **self).encode(encoder)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use matches::assert_matches;
    use std::{f32, f64, fmt, i64, u64};

    pub const CONTEXTS: &[&Context] = &[&Context {}];

    pub fn encode_decode<T: Encodable + Decodable>(ctx: &Context, start: &mut T) -> T {
        let buf = &mut Vec::new();
        let handle_buf = &mut Vec::new();
        Encoder::encode_with_context(ctx, buf, handle_buf, start).expect("Encoding failed");
        let mut out = T::new_empty();
        Decoder::decode_with_context(ctx, buf, handle_buf, &mut out).expect("Decoding failed");
        out
    }

    fn encode_assert_bytes<T: Encodable>(ctx: &Context, mut data: T, encoded_bytes: &[u8]) {
        let buf = &mut Vec::new();
        let handle_buf = &mut Vec::new();
        Encoder::encode_with_context(ctx, buf, handle_buf, &mut data).expect("Encoding failed");
        assert_eq!(&**buf, encoded_bytes);
    }

    fn decode_assert_bytes<T: Decodable + PartialEq + fmt::Debug>(
        ctx: &Context,
        bytes: &[u8],
        expected: &T,
    ) {
        let handle_buf = &mut Vec::new();
        let mut actual = T::new_empty();
        Decoder::decode_with_context(ctx, bytes, handle_buf, &mut actual).expect("Decoding failed");
        assert_eq!(&actual, expected);
    }

    fn assert_identity<T>(mut x: T, cloned: T)
    where
        T: Encodable + Decodable + PartialEq + fmt::Debug,
    {
        for ctx in CONTEXTS {
            assert_eq!(cloned, encode_decode(ctx, &mut x));
        }
    }

    macro_rules! identities { ($($x:expr,)*) => { $(
        assert_identity($x, $x);
    )* } }

    #[test]
    fn encode_decode_byte() {
        identities![0u8, 57u8, 255u8, 0i8, -57i8, 12i8,];
    }

    #[test]
    #[rustfmt::skip]
    fn encode_decode_multibyte() {
        identities![
            0u64, 1u64, u64::MAX, u64::MIN,
            0i64, 1i64, i64::MAX, i64::MIN,
            0f32, 1f32, f32::MAX, f32::MIN,
            0f64, 1f64, f64::MAX, f64::MIN,
        ];
    }

    #[test]
    fn encode_decode_nan() {
        for ctx in CONTEXTS {
            let nan32 = encode_decode(ctx, &mut f32::NAN);
            assert!(nan32.is_nan());

            let nan64 = encode_decode(ctx, &mut f64::NAN);
            assert!(nan64.is_nan());
        }
    }

    #[test]
    fn encode_decode_out_of_line() {
        identities![
            Vec::<i32>::new(),
            vec![1, 2, 3],
            None::<Vec<i32>>,
            Some(Vec::<i32>::new()),
            Some(vec![1, 2, 3]),
            Some(vec![vec![1, 2, 3]]),
            Some(vec![Some(vec![1, 2, 3])]),
            "".to_string(),
            "foo".to_string(),
            None::<String>,
            Some("".to_string()),
            Some("foo".to_string()),
            Some(vec![None, Some("foo".to_string())]),
            vec!["foo".to_string(), "bar".to_string()],
        ];
    }

    #[test]
    fn encode_decode_bits() {
        fidl_bits!(Buttons(u32) {
            PLAY = 1,
            PAUSE = 2,
            STOP = 4,
        });

        assert_eq!(Buttons::from_bits(1), Some(Buttons::PLAY));
        assert_eq!(Buttons::from_bits(12), None);
        assert_eq!(Buttons::STOP.bits(), 4);

        identities![
            Buttons::PLAY,
            Buttons::PAUSE,
            Buttons::STOP,
            Buttons::from_bits(1).expect("should be Play"),
            Buttons::from_bits(Buttons::PAUSE.bits()).expect("should be Pause"),
        ];
    }

    #[test]
    fn encode_decode_enum() {
        fidl_enum!(Animal(i32) {
            Dog = 0,
            Cat = 1,
            Frog = 2,
        });

        assert_eq!(Animal::from_primitive(0), Some(Animal::Dog));
        assert_eq!(Animal::from_primitive(3), None);
        assert_eq!(Animal::Cat.into_primitive(), 1);

        identities![
            Animal::Dog,
            Animal::Cat,
            Animal::Frog,
            Animal::from_primitive(0).expect("should be dog"),
            Animal::from_primitive(Animal::Cat.into_primitive()).expect("should be cat"),
        ];
    }

    #[test]
    fn result_encode_empty_ok_value() {
        identities![(), Ok::<(), i32>(()),];
        for ctx in CONTEXTS {
            // An empty response is represented by () and has zero size.
            encode_assert_bytes(ctx, (), &[]);
            // But in the context of an error result type Result<(), ErrorType>, the
            // () in Ok(()) is treated as an empty struct (with size 1).
            encode_assert_bytes(
                ctx,
                Ok::<(), i32>(()),
                &[
                    0x01, 0x00, 0x00, 0x00, // success ordinal
                    0x00, 0x00, 0x00, 0x00, // success ordinal [cont.]
                    0x08, 0x00, 0x00, 0x00, // 8 bytes (rounded up from 1)
                    0x00, 0x00, 0x00, 0x00, // 0 handles
                    0xff, 0xff, 0xff, 0xff, // present
                    0xff, 0xff, 0xff, 0xff, // present [cont.]
                    0x00, 0x00, 0x00, 0x00, // empty struct + 3 bytes padding
                    0x00, 0x00, 0x00, 0x00, // padding
                ],
            );
        }
    }

    #[test]
    fn result_with_size_non_multiple_of_align() {
        type Res = std::result::Result<(Vec<u8>, bool), u32>;

        identities![
            Res::Ok((vec![], true)),
            Res::Ok((vec![], false)),
            Res::Ok((vec![1, 2, 3, 4, 5], true)),
            Res::Err(7u32),
        ];
    }

    #[test]
    fn result_and_xunion_compat() {
        fidl_xunion! {
            #[derive(Debug, Copy, Clone, Eq, PartialEq)]
            name: OkayOrError,
            members: [
                Okay {
                    ty: u64,
                    ordinal: 1,
                    explicit_ordinal: 1,
                    hashed_ordinal: 123,
                },
                Error {
                    ty: u32,
                    ordinal: 2,
                    explicit_ordinal: 2,
                    hashed_ordinal: 456,
                },
            ],
        };

        for ctx in CONTEXTS {
            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            let mut out: std::result::Result<u64, u32> = Decodable::new_empty();

            Encoder::encode_with_context(ctx, buf, handle_buf, &mut OkayOrError::Okay(42u64))
                .expect("Encoding failed");
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut out).expect("Decoding failed");
            assert_eq!(out, Ok(42));

            Encoder::encode_with_context(ctx, buf, handle_buf, &mut OkayOrError::Error(3u32))
                .expect("Encoding failed");
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut out).expect("Decoding failed");
            assert_eq!(out, Err(3));
        }
    }

    #[test]
    fn result_and_xunion_compat_smaller() {
        fidl_empty_struct!(Empty);
        fidl_xunion! {
            #[derive(Debug, Copy, Clone, Eq, PartialEq)]
            name: OkayOrError,
            members: [
                Okay {
                    ty: Empty,
                    ordinal: 1,
                    explicit_ordinal: 1,
                    hashed_ordinal: 123,
                },
                Error {
                    ty: i32,
                    ordinal: 2,
                    explicit_ordinal: 2,
                    hashed_ordinal: 456,
                },
            ],
        };

        for ctx in CONTEXTS {
            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();

            // result to xunion
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut Ok::<(), i32>(()))
                .expect("Encoding failed");
            let mut out = OkayOrError::new_empty();
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut out).expect("Decoding failed");
            assert_eq!(out, OkayOrError::Okay(Empty {}));

            Encoder::encode_with_context(ctx, buf, handle_buf, &mut Err::<(), i32>(5))
                .expect("Encoding failed");
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut out).expect("Decoding failed");
            assert_eq!(out, OkayOrError::Error(5));

            // xunion to result
            let mut out: std::result::Result<(), i32> = Decodable::new_empty();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut OkayOrError::Okay(Empty {}))
                .expect("Encoding failed");
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut out).expect("Decoding failed");
            assert_eq!(out, Ok(()));

            Encoder::encode_with_context(ctx, buf, handle_buf, &mut OkayOrError::Error(3i32))
                .expect("Encoding failed");
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut out).expect("Decoding failed");
            assert_eq!(out, Err(3));
        }
    }

    #[test]
    fn encode_decode_result() {
        for ctx in CONTEXTS {
            let mut test_result: std::result::Result<String, u32> = Ok("fuchsia".to_string());
            let mut test_result_err: std::result::Result<String, u32> = Err(5);

            match encode_decode(ctx, &mut test_result) {
                Ok(ref out_str) if "fuchsia".to_string() == *out_str => {}
                x => panic!("unexpected decoded value {:?}", x),
            }

            match &encode_decode(ctx, &mut test_result_err) {
                Err(err_code) if *err_code == 5 => {}
                x => panic!("unexpected decoded value {:?}", x),
            }
        }
    }

    #[test]
    fn encode_decode_result_array() {
        use std::result::Result;

        for ctx in CONTEXTS {
            {
                let mut input: [Result<_, u32>; 2] = [Ok("a".to_string()), Ok("bcd".to_string())];
                match encode_decode(ctx, &mut input) {
                    [Ok(ref ok1), Ok(ref ok2)]
                        if *ok1 == "a".to_string() && *ok2 == "bcd".to_string() => {}
                    x => panic!("unexpected decoded value {:?}", x),
                }
            }

            {
                let mut input: [Result<String, u32>; 2] = [Err(7), Err(42)];
                match encode_decode(ctx, &mut input) {
                    [Err(ref err1), Err(ref err2)] if *err1 == 7 && *err2 == 42 => {}
                    x => panic!("unexpected decoded value {:?}", x),
                }
            }

            {
                let mut input = [Ok("abc".to_string()), Err(42)];
                match encode_decode(ctx, &mut input) {
                    [Ok(ref ok1), Err(ref err2)] if *ok1 == "abc".to_string() && *err2 == 42 => {}
                    x => panic!("unexpected decoded value {:?}", x),
                }
            }
        }
    }

    struct Foo {
        byte: u8,
        bignum: u64,
        string: String,
    }

    fidl_struct! {
        name: Foo,
        members: [
            byte {
                ty: u8,
                offset_v1: 0,
            },
            bignum {
                ty: u64,
                offset_v1: 8,
            },
            string {
                ty: String,
                offset_v1: 16,
            },
        ],
        size_v1: 32,
        align_v1: 8,
    }

    #[test]
    fn encode_decode_struct() {
        for ctx in CONTEXTS {
            let out_foo = encode_decode(
                ctx,
                &mut Some(Box::new(Foo { byte: 5, bignum: 22, string: "hello world".to_string() })),
            )
            .expect("should be some");

            assert_eq!(out_foo.byte, 5);
            assert_eq!(out_foo.bignum, 22);
            assert_eq!(out_foo.string, "hello world");

            let out_foo: Option<Box<Foo>> = encode_decode(ctx, &mut Box::new(None));
            assert!(out_foo.is_none());
        }
    }

    #[test]
    fn decode_struct_with_invalid_padding_fails() {
        for ctx in CONTEXTS {
            let foo = &mut Foo { byte: 0, bignum: 0, string: String::new() };
            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, foo).expect("Encoding failed");

            buf[1] = 42;
            let out = &mut Foo::new_empty();
            let result = Decoder::decode_with_context(ctx, buf, handle_buf, out);
            assert_matches!(
                result,
                Err(Error::NonZeroPadding { padding_start: 1, non_zero_pos: 1 })
            );
        }
    }

    #[test]
    fn encode_decode_tuple() {
        for ctx in CONTEXTS {
            let mut start: (&mut u8, &mut u64, &mut String) =
                (&mut 5, &mut 10, &mut "foo".to_string());
            let mut out: (u8, u64, String) = Decodable::new_empty();

            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut start)
                .expect("Encoding failed");
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut out).expect("Decoding failed");

            assert_eq!(*start.0, out.0);
            assert_eq!(*start.1, out.1);
            assert_eq!(*start.2, out.2);
        }
    }

    #[test]
    fn encode_decode_struct_as_tuple() {
        for ctx in CONTEXTS {
            let mut start = Foo { byte: 5, bignum: 10, string: "foo".to_string() };
            let mut out: (u8, u64, String) = Decodable::new_empty();

            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut start)
                .expect("Encoding failed");
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut out).expect("Decoding failed");

            assert_eq!(start.byte, out.0);
            assert_eq!(start.bignum, out.1);
            assert_eq!(start.string, out.2);
        }
    }

    #[test]
    fn encode_decode_tuple_as_struct() {
        for ctx in CONTEXTS {
            let mut start = (&mut 5u8, &mut 10u64, &mut "foo".to_string());
            let mut out: Foo = Decodable::new_empty();

            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut start)
                .expect("Encoding failed");
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut out).expect("Decoding failed");

            assert_eq!(*start.0, out.byte);
            assert_eq!(*start.1, out.bignum);
            assert_eq!(*start.2, out.string);
        }
    }

    #[test]
    fn encode_decode_tuple_msg() {
        for ctx in CONTEXTS {
            let mut body_start = (&mut "foo".to_string(), &mut 5);
            let mut body_out: (String, u8) = Decodable::new_empty();

            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut body_start).unwrap();
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut body_out).unwrap();

            assert_eq!(body_start.0, &mut body_out.0);
            assert_eq!(body_start.1, &mut body_out.1);
        }
    }

    pub struct MyTable {
        pub num: Option<i32>,
        pub num_none: Option<i32>,
        pub string: Option<String>,
        pub handle: Option<Handle>,
    }

    fidl_table! {
        name: MyTable,
        members: {
            num {
                ty: i32,
                ordinal: 1,
            },
            num_none {
                ty: i32,
                ordinal: 2,
            },
            string {
                ty: String,
                ordinal: 3,
            },
            handle {
                ty: Handle,
                ordinal: 4,
            },
        },
    }

    #[allow(unused)]
    struct EmptyTableCompiles {}
    fidl_table! {
        name: EmptyTableCompiles,
        members: {},
    }

    struct TablePrefix {
        num: Option<i32>,
        num_none: Option<i32>,
    }

    fidl_table! {
        name: TablePrefix,
        members: {
            num {
                ty: i32,
                ordinal: 1,
            },
            num_none {
                ty: i32,
                ordinal: 2,
            },
        },
    }

    #[test]
    fn empty_table() {
        let mut table: MyTable = MyTable::empty();
        assert_eq!(None, table.num);
        table = MyTable { num: Some(32), ..MyTable::empty() };
        assert_eq!(Some(32), table.num);
        assert_eq!(None, table.string);
    }

    #[test]
    fn table_encode_prefix_decode_full() {
        for ctx in CONTEXTS {
            let mut table_prefix_in = TablePrefix { num: Some(5), num_none: None };
            let mut table_out: MyTable = Decodable::new_empty();

            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut table_prefix_in).unwrap();
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut table_out).unwrap();

            assert_eq!(table_out.num, Some(5));
            assert_eq!(table_out.num_none, None);
            assert_eq!(table_out.string, None);
            assert_eq!(table_out.handle, None);
        }
    }

    #[test]
    fn table_encode_omits_none_tail() {
        for ctx in CONTEXTS {
            // "None" fields at the tail of a table shouldn't be encoded at all.
            let mut table_in = MyTable {
                num: Some(5),
                // These fields should all be omitted in the encoded repr,
                // allowing decoding of the prefix to succeed.
                num_none: None,
                string: None,
                handle: None,
            };
            let mut table_prefix_out: TablePrefix = Decodable::new_empty();

            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut table_in).unwrap();
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut table_prefix_out).unwrap();

            assert_eq!(table_prefix_out.num, Some(5));
            assert_eq!(table_prefix_out.num_none, None);
        }
    }

    #[test]
    fn table_decode_fails_on_unrecognized_tail() {
        for ctx in CONTEXTS {
            let mut table_in = MyTable {
                num: Some(5),
                num_none: None,
                string: Some("foo".to_string()),
                handle: None,
            };
            let mut table_prefix_out: TablePrefix = Decodable::new_empty();

            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut table_in).unwrap();
            let result = Decoder::decode_with_context(ctx, buf, handle_buf, &mut table_prefix_out);
            assert_matches!(result, Err(Error::UnknownTableField));
        }
    }

    #[derive(Debug, PartialEq)]
    pub struct SimpleTable {
        x: Option<i64>,
        y: Option<i64>,
    }

    fidl_table! {
        name: SimpleTable,
        members: {
            x {
                ty: i64,
                ordinal: 1,
            },
            y {
                ty: i64,
                ordinal: 5,
            },
        },
    }

    #[derive(Debug, PartialEq)]
    pub struct TableWithStringAndVector {
        foo: Option<String>,
        bar: Option<i32>,
        baz: Option<Vec<u8>>,
    }

    fidl_table! {
        name: TableWithStringAndVector,
        members: {
            foo {
                ty: String,
                ordinal: 1,
            },
            bar {
                ty: i32,
                ordinal: 2,
            },
            baz {
                ty: Vec<u8>,
                ordinal: 3,
            },
        },
    }

    #[test]
    fn table_golden_simple_table_with_xy() {
        let simple_table_with_xy: &[u8] = &[
            5, 0, 0, 0, 0, 0, 0, 0, // max ordinal
            255, 255, 255, 255, 255, 255, 255, 255, // alloc present
            8, 0, 0, 0, 0, 0, 0, 0, // envelope 1: num bytes / num handles
            255, 255, 255, 255, 255, 255, 255, 255, // alloc present
            0, 0, 0, 0, 0, 0, 0, 0, // envelope 2: num bytes / num handles
            0, 0, 0, 0, 0, 0, 0, 0, // no alloc
            0, 0, 0, 0, 0, 0, 0, 0, // envelope 3: num bytes / num handles
            0, 0, 0, 0, 0, 0, 0, 0, // no alloc
            0, 0, 0, 0, 0, 0, 0, 0, // envelope 4: num bytes / num handles
            0, 0, 0, 0, 0, 0, 0, 0, // no alloc
            8, 0, 0, 0, 0, 0, 0, 0, // envelope 5: num bytes / num handles
            255, 255, 255, 255, 255, 255, 255, 255, // alloc present
            42, 0, 0, 0, 0, 0, 0, 0, // field X
            67, 0, 0, 0, 0, 0, 0, 0, // field Y
        ];
        for ctx in CONTEXTS {
            encode_assert_bytes(
                ctx,
                SimpleTable { x: Some(42), y: Some(67) },
                simple_table_with_xy,
            );
        }
    }

    #[test]
    fn table_golden_simple_table_with_y() {
        let simple_table_with_y: &[u8] = &[
            5, 0, 0, 0, 0, 0, 0, 0, // max ordinal
            255, 255, 255, 255, 255, 255, 255, 255, // alloc present
            0, 0, 0, 0, 0, 0, 0, 0, // envelope 1: num bytes / num handles
            0, 0, 0, 0, 0, 0, 0, 0, // no alloc
            0, 0, 0, 0, 0, 0, 0, 0, // envelope 2: num bytes / num handles
            0, 0, 0, 0, 0, 0, 0, 0, // no alloc
            0, 0, 0, 0, 0, 0, 0, 0, // envelope 3: num bytes / num handles
            0, 0, 0, 0, 0, 0, 0, 0, // no alloc
            0, 0, 0, 0, 0, 0, 0, 0, // envelope 4: num bytes / num handles
            0, 0, 0, 0, 0, 0, 0, 0, // no alloc
            8, 0, 0, 0, 0, 0, 0, 0, // envelope 5: num bytes / num handles
            255, 255, 255, 255, 255, 255, 255, 255, // alloc present
            67, 0, 0, 0, 0, 0, 0, 0, // field Y
        ];
        for ctx in CONTEXTS {
            encode_assert_bytes(ctx, SimpleTable { x: None, y: Some(67) }, simple_table_with_y);
        }
    }

    #[test]
    fn table_golden_string_and_vector_hello_27() {
        let table_with_string_and_vector_hello_27: &[u8] = &[
            2, 0, 0, 0, 0, 0, 0, 0, // max ordinal
            255, 255, 255, 255, 255, 255, 255, 255, // alloc present
            24, 0, 0, 0, 0, 0, 0, 0, // envelope 1: num bytes / num handles
            255, 255, 255, 255, 255, 255, 255, 255, // envelope 1: alloc present
            8, 0, 0, 0, 0, 0, 0, 0, // envelope 2: num bytes / num handles
            255, 255, 255, 255, 255, 255, 255, 255, // envelope 2: alloc present
            5, 0, 0, 0, 0, 0, 0, 0, // element 1: length
            255, 255, 255, 255, 255, 255, 255, 255, // element 1: alloc present
            104, 101, 108, 108, 111, 0, 0, 0, // element 1: hello
            27, 0, 0, 0, 0, 0, 0, 0, // element 2: value
        ];
        for ctx in CONTEXTS {
            encode_assert_bytes(
                ctx,
                TableWithStringAndVector {
                    foo: Some("hello".to_string()),
                    bar: Some(27),
                    baz: None,
                },
                table_with_string_and_vector_hello_27,
            );
        }
    }

    #[test]
    fn table_golden_empty_table() {
        let empty_table: &[u8] = &[
            0, 0, 0, 0, 0, 0, 0, 0, // max ordinal
            255, 255, 255, 255, 255, 255, 255, 255, // alloc present
        ];

        for ctx in CONTEXTS {
            encode_assert_bytes(ctx, SimpleTable { x: None, y: None }, empty_table);
        }
    }

    struct TableWithGaps {
        second: Option<i32>,
        fourth: Option<i32>,
    }

    fidl_table! {
        name: TableWithGaps,
        members: {
            second {
                ty: i32,
                ordinal: 2,
            },
            fourth {
                ty: i32,
                ordinal: 4,
            },
        },
    }

    #[test]
    fn encode_decode_table_with_gaps() {
        for ctx in CONTEXTS {
            let mut table = TableWithGaps { second: Some(1), fourth: Some(2) };
            let table_out = encode_decode(ctx, &mut table);
            assert_eq!(table_out.second, Some(1));
            assert_eq!(table_out.fourth, Some(2));
        }
    }

    #[test]
    fn encode_empty_envelopes_for_reserved_table_fields() {
        for ctx in CONTEXTS {
            let mut table = TableWithGaps { second: Some(1), fourth: Some(2) };
            let buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, &mut Vec::new(), &mut table).unwrap();

            // Expected layout:
            //     0x00 table header
            //     0x10 envelope 1 (reserved)
            //     0x20 envelope 2 (second)
            //     0x30 envelope 3 (reserved)
            //     0x40 envelope 4 (fourth)
            assert_eq!(&buf[0x10..0x20], &[0; 16]);
            assert_eq!(&buf[0x30..0x40], &[0; 16]);
        }
    }

    #[test]
    fn decode_fails_without_reserved_table_fields() {
        struct TableWithoutGaps {
            first: Option<i32>,
            second: Option<i32>,
        }
        fidl_table! {
            name: TableWithoutGaps,
            members: {
                first {
                    ty: i32,
                    ordinal: 1,
                },
                second {
                    ty: i32,
                    ordinal: 2,
                },
            },
        }

        for ctx in CONTEXTS {
            // Encode _without_ gaps, then attempt to decode _with_ gaps.
            let mut table = TableWithoutGaps { first: Some(1), second: Some(2) };
            let buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, &mut Vec::new(), &mut table).unwrap();

            let mut out = TableWithGaps::new_empty();
            let result = Decoder::decode_with_context(ctx, buf, &mut Vec::new(), &mut out);
            assert_matches!(result, Err(Error::UnknownTableField));
        }
    }

    #[derive(Debug, PartialEq)]
    pub struct Int64Struct {
        x: u64,
    }
    fidl_struct! {
        name: Int64Struct,
        members: [
            x {
                ty: u64,
                offset_v1: 0,
            },
        ],
        size_v1: 8,
        align_v1: 8,
    }
    // Ensure single-variant xunion compiles (no irrefutable pattern errors).
    fidl_xunion! {
        #[derive(Debug, PartialEq)]
        name: SingleVariantXUnion,
        members: [
            B {
                ty: bool,
                ordinal: 1,
                explicit_ordinal: 1,
                hashed_ordinal: 123,
            },
        ],
    }

    fidl_xunion! {
        #[derive(Debug, PartialEq)]
        name: TestSampleXUnion,
        members: [
            U {
                ty: u32,
                ordinal: 0x29df47a5,
                explicit_ordinal: 1,
                hashed_ordinal: 0x29df47a5,
            },
            St {
                ty: SimpleTable,
                ordinal: 0x6f317664,
                explicit_ordinal: 2,
                hashed_ordinal: 0x6f317664,
            },
        ],
        unknown_member: __UnknownVariant,
    }

    fidl_xunion! {
        #[derive(Debug, PartialEq)]
        name: TestSampleXUnionStrict,
        members: [
            U {
                ty: u32,
                ordinal: 0x29df47a5,
                explicit_ordinal: 1,
                hashed_ordinal: 0x29df47a5,
            },
            St {
                ty: SimpleTable,
                ordinal: 0x6f317664,
                explicit_ordinal: 1,
                hashed_ordinal: 0x6f317664,
            },
        ],
    }

    fidl_xunion! {
        #[derive(Debug, PartialEq)]
        name: TestSampleXUnionExpanded,
        members: [
            SomethinElse {
                ty: Handle,
                ordinal: 55,
                explicit_ordinal: 1,
                hashed_ordinal: 55,
            },
        ],
        unknown_member: __UnknownVariant,
    }

    #[test]
    fn xunion_golden_u() {
        let xunion_u_bytes = &[
            0xa5, 0x47, 0xdf, 0x29, 0x00, 0x00, 0x00, 0x00, // xunion discriminator + padding
            0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // num bytes + num handles
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, // presence indicator
            0xef, 0xbe, 0xad, 0xde, 0x00, 0x00, 0x00, 0x00, // content + padding
        ];

        for ctx in CONTEXTS {
            encode_assert_bytes(ctx, TestSampleXUnion::U(0xdeadbeef), xunion_u_bytes);
            encode_assert_bytes(ctx, TestSampleXUnionStrict::U(0xdeadbeef), xunion_u_bytes);

            // The nullable representation Option<Box<T>> has the same layout.
            encode_assert_bytes(
                ctx,
                Some(Box::new(TestSampleXUnion::U(0xdeadbeef))),
                xunion_u_bytes,
            );
            encode_assert_bytes(
                ctx,
                Some(Box::new(TestSampleXUnionStrict::U(0xdeadbeef))),
                xunion_u_bytes,
            );
        }
    }

    #[test]
    fn xunion_golden_read_both_ordinals() {
        let hashed_bytes = &[
            0xa5, 0x47, 0xdf, 0x29, 0x00, 0x00, 0x00, 0x00, // hashed xunion ordinal
            0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // num bytes + num handles
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, // presence indicator
            0xef, 0xbe, 0xad, 0xde, 0x00, 0x00, 0x00, 0x00, // content + padding
        ];

        let explicit_bytes = &[
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // explicit xunion ordinal
            0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // num bytes + num handles
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, // presence indicator
            0xef, 0xbe, 0xad, 0xde, 0x00, 0x00, 0x00, 0x00, // content + padding
        ];

        for ctx in CONTEXTS {
            // Decoding understands both hashed and explicit bytes. Encoding uses only the value
            // specified in the "ordinal" field, which for this xunion is the hashed ordinal
            {
                let xunion_obj = TestSampleXUnion::U(0xdeadbeef);
                decode_assert_bytes(ctx, hashed_bytes, &xunion_obj);
                encode_assert_bytes(ctx, xunion_obj, hashed_bytes);
            }
            {
                let xunion_obj = TestSampleXUnion::U(0xdeadbeef);
                decode_assert_bytes(ctx, explicit_bytes, &xunion_obj);
                encode_assert_bytes(ctx, xunion_obj, hashed_bytes);
            }
        }
    }

    #[test]
    fn xunion_golden_null() {
        for ctx in CONTEXTS {
            encode_assert_bytes(ctx, None::<Box<TestSampleXUnion>>, &[0; 24]);
            encode_assert_bytes(ctx, None::<Box<TestSampleXUnionStrict>>, &[0; 24]);
        }
    }

    #[test]
    fn encode_decode_transaction_msg() {
        for ctx in CONTEXTS {
            let header = TransactionHeader { tx_id: 4, ordinal: 6, flags: [0; 3], magic_number: 1 };
            let body = "hello".to_string();

            let start = &mut TransactionMessage { header, body: &mut body.clone() };

            let (buf, handles) = (&mut vec![], &mut vec![]);
            Encoder::encode_with_context(ctx, buf, handles, start).expect("Encoding failed");

            let (out_header, out_buf) =
                decode_transaction_header(&**buf).expect("Decoding header failed");
            assert_eq!(header, out_header);

            let mut body_out = String::new();
            Decoder::decode_into(&header, out_buf, handles, &mut body_out)
                .expect("Decoding body failed");
            assert_eq!(body, body_out);
        }
    }

    #[test]
    fn array_of_arrays() {
        for ctx in CONTEXTS {
            let mut input = &mut [&mut [1u32, 2, 3, 4, 5], &mut [5, 4, 3, 2, 1]];
            let (bytes, handles) = (&mut vec![], &mut vec![]);
            assert!(Encoder::encode_with_context(ctx, bytes, handles, &mut input).is_ok());

            let mut output = <[[u32; 5]; 2]>::new_empty();
            Decoder::decode_with_context(ctx, bytes, handles, &mut output).expect(
                format!(
                    "Array decoding failed\n\
                     bytes: {:X?}",
                    bytes
                )
                .as_str(),
            );

            assert_eq!(
                input,
                output.iter_mut().map(|v| v.as_mut()).collect::<Vec<_>>().as_mut_slice()
            );
        }
    }

    #[test]
    fn xunion_with_out_of_line_data() {
        fidl_xunion! {
            #[derive(Debug, PartialEq)]
            name: XUnion,
            members: [
                Variant {
                    ty: Vec<u8>,
                    ordinal: 1,
                    explicit_ordinal: 1,
                    hashed_ordinal: 123,
                },
            ],
            unknown_member: __UnknownVariant,
        }

        identities![
            XUnion::Variant(vec![1, 2, 3]),
            Some(Box::new(XUnion::Variant(vec![1, 2, 3]))),
            None::<Box<XUnion>>,
        ];
    }

    #[test]
    fn strict_xunion_rejects_unknown_ordinal() {
        fidl_xunion! {
            #[derive(Debug, PartialEq)]
            name: StrictBoolXUnion,
            members: [
                B {
                    ty: bool,
                    ordinal: 12345,
                    explicit_ordinal: 1,
                    hashed_ordinal: 12345,
                },
            ],
        }

        for ctx in CONTEXTS {
            let mut input = TestSampleXUnion::U(1);
            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut input).unwrap();

            let mut strict_xunion = StrictBoolXUnion::new_empty();
            let result = Decoder::decode_with_context(ctx, buf, handle_buf, &mut strict_xunion);
            assert_matches!(result, Err(Error::UnknownUnionTag));
        }
    }

    #[test]
    fn xunion_with_64_bit_ordinal() {
        fidl_xunion! {
            #[derive(Debug, Copy, Clone, Eq, PartialEq)]
            name: BigOrdinal,
            members: [
                X {
                    ty: u64,
                    ordinal: 0xffffffffu64,
                    explicit_ordinal: 1,
                    hashed_ordinal: 0xffffffffu64,
                },
            ],
        };

        for ctx in CONTEXTS {
            let mut x = BigOrdinal::X(0);
            assert_eq!(x.ordinal(), 0xffffffffu64);
            assert_eq!(encode_decode(ctx, &mut x).ordinal(), 0xffffffffu64);
        }
    }

    #[test]
    fn extra_data_is_disallowed() {
        for ctx in CONTEXTS {
            let mut output = ();
            assert_matches!(
                Decoder::decode_with_context(ctx, &[0], &mut [], &mut output),
                Err(Error::ExtraBytes)
            );
            assert_matches!(
                Decoder::decode_with_context(ctx, &[], &mut [Handle::invalid()], &mut output),
                Err(Error::ExtraHandles)
            );
        }
    }

    #[test]
    fn encode_default_context() {
        let buf = &mut Vec::new();
        Encoder::encode(buf, &mut Vec::new(), &mut 1u8).expect("Encoding failed");
        assert_eq!(&**buf, &[1u8, 0, 0, 0, 0, 0, 0, 0]);
    }
}

#[cfg(target_os = "fuchsia")]
#[cfg(test)]
mod zx_test {
    use super::test::*;
    use super::*;
    use crate::handle::AsHandleRef;
    //use std::{f32, f64, fmt, i64, u64};
    use fuchsia_zircon as zx;

    #[test]
    fn encode_handle() {
        for ctx in CONTEXTS {
            let mut handle = Handle::from(zx::Port::create().expect("Port creation failed"));
            let raw_handle = handle.raw_handle();

            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut handle)
                .expect("Encoding failed");

            assert!(handle.is_invalid());

            let mut handle_out = Handle::new_empty();
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut handle_out)
                .expect("Decoding failed");

            assert_eq!(raw_handle, handle_out.raw_handle());
        }
    }

    #[test]
    fn encode_decode_table() {
        for ctx in CONTEXTS {
            // create a random handle to encode and then decode.
            let handle = zx::Vmo::create(1024).expect("vmo creation failed");
            let raw_handle = handle.raw_handle();
            let mut starting_table = MyTable {
                num: Some(5),
                num_none: None,
                string: Some("foo".to_string()),
                handle: Some(handle.into_handle()),
            };
            let table_out = encode_decode(ctx, &mut starting_table);
            assert_eq!(table_out.num, Some(5));
            assert_eq!(table_out.num_none, None);
            assert_eq!(table_out.string, Some("foo".to_string()));
            assert_eq!(table_out.handle.unwrap().raw_handle(), raw_handle);
        }
    }

    #[test]
    fn flexible_xunion_unknown_variant_transparent_passthrough() {
        for ctx in CONTEXTS {
            let handle = Handle::from(zx::Port::create().expect("Port creation failed"));
            let raw_handle = handle.raw_handle();

            let mut input = TestSampleXUnionExpanded::SomethinElse(handle);
            // encode expanded and decode as xunion w/ missing variant
            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut input)
                .expect("Encoding TestSampleXUnionExpanded failed");

            let mut intermediate_missing_variant = TestSampleXUnion::new_empty();
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut intermediate_missing_variant)
                .expect("Decoding TestSampleXUnion failed");

            // Ensure we've recorded the unknown variant
            if let TestSampleXUnion::__UnknownVariant { .. } = intermediate_missing_variant {
                // ok
            } else {
                panic!("unexpected variant")
            }

            let buf = &mut Vec::new();
            let handle_buf = &mut Vec::new();
            Encoder::encode_with_context(ctx, buf, handle_buf, &mut intermediate_missing_variant)
                .expect("encoding unknown variant failed");

            let mut out = TestSampleXUnionExpanded::new_empty();
            Decoder::decode_with_context(ctx, buf, handle_buf, &mut out)
                .expect("Decoding final output failed");

            if let TestSampleXUnionExpanded::SomethinElse(handle_out) = out {
                assert_eq!(raw_handle, handle_out.raw_handle());
            } else {
                panic!("wrong final variant")
            }
        }
    }

    #[test]
    fn encode_epitaph() {
        for ctx in CONTEXTS {
            assert_eq!(
                EpitaphBody { error: zx::Status::UNAVAILABLE },
                encode_decode(ctx, &mut EpitaphBody { error: zx::Status::UNAVAILABLE })
            );
        }
    }
}
