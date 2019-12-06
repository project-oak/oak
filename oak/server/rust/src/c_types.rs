#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

pub type blkcnt_t = i64;
pub type blksize_t = c_long;
pub type c_char = i8;
pub type c_double = f64;
pub type c_float = f32;
pub type c_int = i32;
pub type c_long = i32;
pub type c_longlong = i64;
pub type c_schar = i8;
pub type c_short = i16;
pub type c_uchar = u8;
pub type c_uint = u32;
pub type c_ulong = u32;
pub type c_ulonglong = u64;
pub type c_ushort = u16;
pub type cc_t = c_uchar;
pub type clock_t = c_longlong;
pub type dev_t = u64;
pub type gid_t = u32;
pub type in_addr_t = u32;
pub type in_port_t = u16;
pub type ino_t = u64;
pub type intmax_t = i64;
pub type intptr_t = isize;
pub type mode_t = u32;
pub type nfds_t = c_ulong;
pub type nlink_t = u64;
pub type off_t = i64;
pub type pid_t = i32;
pub type ptrdiff_t = isize;
pub type sighandler_t = size_t;
pub type sigset_t = c_uchar;
pub type size_t = usize;
pub type ssize_t = isize;
pub type suseconds_t = c_longlong;
pub type time_t = c_longlong;
pub type uid_t = u32;
pub type uintmax_t = u64;
pub type uintptr_t = usize;

#[repr(u8)]
#[allow(missing_copy_implementations)]
#[allow(missing_debug_implementations)]
pub enum c_void {
    // Two dummy variants so the #[repr] attribute can be used.
    #[doc(hidden)]
    __variant1,
    #[doc(hidden)]
    __variant2,
}
