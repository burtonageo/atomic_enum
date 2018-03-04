use core::sync::atomic::{
	AtomicI8, AtomicI16, AtomicI32, AtomicI64,
	AtomicU8, AtomicU16, AtomicU32, AtomicU64,
	AtomicIsize, Ordering};

impl_atomic_enum_repr!(AtomicI8, i8);
impl_atomic_enum_repr!(AtomicI16, i16);
impl_atomic_enum_repr!(AtomicI32, i32);
impl_atomic_enum_repr!(AtomicI64, i64);

impl_atomic_enum_repr!(AtomicU8, u8);
impl_atomic_enum_repr!(AtomicU16, u16);
impl_atomic_enum_repr!(AtomicU32, u32);
impl_atomic_enum_repr!(AtomicU64, u64);

impl_atomic_enum_repr!(AtomicIsize, isize);
