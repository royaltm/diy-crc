//! Template functions, traits and macros to build your own bit-by-bit CRC implementations.
//!
//! <https://reveng.sourceforge.io/crc-catalogue/all.htm>
//!
//! Some example implementations:
//!
//! ```
//! use diy_crc::*;
//! impl_crc!(Crc5Usb{u8} width=5 poly=0x05 init=0x1f refin=true refout=true xorout=0x1f check=0x19 residue=0x06 name="CRC-5/USB");
//! impl_crc!(MyCrc7{u8} width=7 poly=0x07 init=0x7f refin=true refout=true xorout=0x00 check=0x14);
//! impl_crc!(Crc7Mmc{u8} width=7 poly=0x09 init=0x00 refin=false refout=false xorout=0x00 check=0x75 residue=0x00 name="CRC-7/MMC");
//! impl_crc!(Crc7Rohc{u8} width=7 poly=0x4f init=0x7f refin=true refout=true xorout=0x00 check=0x53 residue=0x00 name="CRC-7/ROHC");
//! impl_crc!(Crc7Umts{u8} width=7 poly=0x45 init=0x00 refin=false refout=false xorout=0x00 check=0x61 residue=0x00 name="CRC-7/UMTS");
//! impl_crc!(Crc8I4321{u8} width=8 poly=0x07 init=0x00 refin=false refout=false xorout=0x55 check=0xa1 residue=0xac name="CRC-8/I-432-1");
//! impl_crc!(Crc8Rohc{u8} width=8 poly=0x07 init=0xff refin=true refout=true xorout=0x00 check=0xd0 residue=0x00 name="CRC-8/ROHC");
//! impl_crc!(Crc11Umts{u16} width=11 poly=0x307 init=0x000 refin=false refout=false xorout=0x000 check=0x061 residue=0x000 name="CRC-11/UMTS");
//! impl_crc!(Crc12Umts{u16} width=12 poly=0x80f init=0x000 refin=false refout=true xorout=0x000 check=0xdaf residue=0x000 name="CRC-12/UMTS");
//! impl_crc!(Crc16Umts{u16} width=16 poly=0x8005 init=0x0000 refin=false refout=false xorout=0x0000 check=0xfee8 residue=0x0000 name="CRC-16/UMTS");
//! impl_crc!(Crc32Cksum{u32} width=32 poly=0x04c11db7 init=0x00000000 refin=false refout=false xorout=0xffffffff check=0x765e7680 residue=0xc704dd7b name="CRC-32/CKSUM");
//! impl_crc!(Crc32Iscsi{u32} width=32 poly=0x1edc6f41 init=0xffffffff refin=true refout=true xorout=0xffffffff check=0xe3069283 residue=0xb798b438 name="CRC-32/ISCSI");
//! impl_crc!(Crc32IsoHdlc{u32} width=32 poly=0x04c11db7 init=0xffffffff refin=true refout=true xorout=0xffffffff check=0xcbf43926 residue=0xdebb20e3 name="CRC-32/ISO-HDLC");
//! impl_crc!(Crc32Jamcrc{u32} width=32 poly=0x04c11db7 init=0xffffffff refin=true refout=true xorout=0x00000000 check=0x340bc6d9 residue=0x00000000 name="CRC-32/JAMCRC");
//! impl_crc!(Crc32Mef{u32} width=32 poly=0x741b8cd7 init=0xffffffff refin=true refout=true xorout=0x00000000 check=0xd2c22f51 residue=0x00000000 name="CRC-32/MEF");
//! impl_crc!(Crc32Mpeg2{u32} width=32 poly=0x04c11db7 init=0xffffffff refin=false refout=false xorout=0x00000000 check=0x0376e6e7 residue=0x00000000 name="CRC-32/MPEG-2");
//! impl_crc!(Crc32xfer{u32} width=32 poly=0x000000af init=0x00000000 refin=false refout=false xorout=0x00000000 check=0xbd0be338 residue=0x00000000 name="CRC-32/XFER");
//! impl_crc!(Crc64Redis{u64} width=64 poly=0xad93d23594c935a9 init=0x0000000000000000 refin=true refout=true xorout=0x0000000000000000 check=0xe9c6d914c4b8d9ca residue=0x0000000000000000 name="CRC-64/REDIS");
//! ```
use core::ops::{Shl, Shr, BitXorAssign};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitOrder {
    MsbToLsb,
    LsbToMsb
}

impl BitOrder {
    pub fn is_msb_first(self) -> bool {
        self == BitOrder::MsbToLsb
    }
    pub fn is_lsb_first(self) -> bool {
        self == BitOrder::LsbToMsb
    }
}

/// CRC implementation tools.
pub trait CoreCrc {
    /// The CRC register type.
    type Register;
    /// The number of BITS in the CRC algorithm.
    const BITS: usize;
    /// The CRC polynomial.
    ///
    /// Polynomial value should be right-aligned if BITS is lower than register bit width.
    const POLYNOMIAL: Self::Register;
    /// CRC initial value.
    ///
    /// INIT value should be right-aligned if BITS is lower than register bit width.
    const INIT: Self::Register;
    /// Whether the resulting CRC is reflected (bit-reversed).
    const REFLECTED: bool;
    /// The read order of bits in data characters.
    const DATA_BIT_ORDER: BitOrder;
    /// The XOROUT value.
    const XOROUT: Self::Register;
    /// Continue calculating CRC with data.
    fn crc_with<T>(crc: Self::Register, data: &[T]) -> Self::Register
        where Self::Register: From<T>, T: Copy + ReverseBits;
    /// Calculate CRC from data and INIT.
    fn crc<T>(data: &[T]) -> Self::Register
        where Self::Register: From<T>, T: Copy + ReverseBits;
    /// Return whether the resulting CRC is reflected (bit-reversed).
    fn is_reflected() -> bool { Self::REFLECTED }
    /// Return the read order of bits in data characters.
    fn data_bit_order() -> BitOrder { Self::DATA_BIT_ORDER }
    /// Return algorithm INIT value.
    fn init() -> Self::Register { Self::INIT }
    /// Return XOROUT value.
    fn xorout() -> Self::Register { Self::XOROUT }
    /// The name of the algorithm.
    ///
    /// Implementation is optional.
    fn name() -> &'static str { unimplemented!() }
    /// A function to validate the algorithm. Return `check` value.
    ///
    /// Implementation is optional.
    fn validate() -> Self::Register { unimplemented!() }
}

/// Helper macro for [CoreCrc] trait implementation.
///
/// The macro will define a unit struct with a given visibility and name
///  and implement [CoreCrc] for the created type with the given parameters.
///
/// The detailed parameter description can be read here:
///
/// <https://reveng.sourceforge.io/crc-catalogue/all.htm#crc.legend.params>
///
/// `check`, `residue` and `name` parameters are optional and can be omitted.
///
/// If the `name` parameter is provided the struct will implement [fmt::Display](core::fmt::Display)
/// and the `CoreCrc` trait will have [`::name()`](CoreCrc::name) function implemented.
/// 
/// If the `check` parameter is provided the `CoreCrc` trait will have
/// [`::validate()`](CoreCrc::validate) function implemented.
/// 
/// For example:
///
/// ```
/// use diy_crc::*;
/// impl_crc!(pub Crc5Usb{u8} width=5 poly=0x05 init=0x1f refin=true refout=true xorout=0x1f check=0x19 residue=0x06 name="CRC-5/USB");
/// ```
#[macro_export] macro_rules! impl_crc {
    ($pub:vis $id:ident{$reg:ty}
     width=$bits:literal
     poly=$poly:literal
     init=$init:literal
     refin=$refin:tt
     refout=$refout:tt
     xorout=$xorout:literal
     $(check=$check:literal)?
     $(residue=$residue:literal)?
     $(name=$name:literal)?) => {
        impl_crc!(@refin=$refin @refout=$refout $pub $id,
                  $bits, $reg, $poly, $init, $xorout
                  $(, check=$check)?
                  $(, name=$name)?);
        $(
            impl core::fmt::Display for $id {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    f.write_str($name)
                }
            }
        )?
    };

    (@refin=false @refout=false $pub:vis $id:ident,
        $bits:literal, $reg:ty, $poly:literal, $init:literal, $xorout:literal
        $(, check=$check:literal)?
        $(, name=$name:literal)?
    ) => {
        impl_crc!(@crc crc, $pub $id, $bits, $reg, $poly, $init, $xorout,
                  $crate::crc::BitOrder::MsbToLsb,
                  $init, false
                  $(, check=$check)?
                  $(, name=$name)?);
    };

    (@refin=true @refout=false $pub:vis $id:ident,
        $bits:literal, $reg:ty, $poly:literal, $init:literal, $xorout:literal
        $(, check=$check:literal)?
        $(, name=$name:literal)?
    ) => {
        impl_crc!(@crc crc_refin, $pub $id, $bits, $reg, $poly, $init, $xorout,
                  $crate::crc::BitOrder::LsbToMsb,
                  $init, false
                  $(, check=$check)?
                  $(, name=$name)?);
    };

    (@refin=false @refout=true $pub:vis $id:ident,
        $bits:literal, $reg:ty, $poly:literal, $init:literal, $xorout:literal
        $(, check=$check:literal)?
        $(, name=$name:literal)?
    ) => {
        impl_crc!(@crc crc_refout, $pub $id, $bits, $reg, $poly, $init, $xorout,
                  $crate::crc::BitOrder::MsbToLsb,
                  ($init << (core::mem::size_of::<$reg>()*8 - $bits)).reverse_bits(), true
                  $(, check=$check)?
                  $(, name=$name)?);
    };

    (@refin=true @refout=true $pub:vis $id:ident,
        $bits:literal, $reg:ty, $poly:literal, $init:literal, $xorout:literal
        $(, check=$check:literal)?
        $(, name=$name:literal)?
    ) => {
        impl_crc!(@crc crc_reflect, $pub $id, $bits, $reg, $poly, $init, $xorout,
                  $crate::crc::BitOrder::LsbToMsb,
                  ($init << (core::mem::size_of::<$reg>()*8 - $bits)).reverse_bits(), true
                  $(, check=$check)?
                  $(, name=$name)?);
    };

    (@crc
     $fun:ident,
     $pub:vis $id:ident,
     $bits:literal,
     $reg:ty,
     $poly:literal,
     $init:literal,
     $xorout:literal,
     $bitord:expr,
     $rinit:expr,
     $refout:literal
     $(, check=$check:literal)?
     $(, name=$name:literal)?
    ) => {

        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        $pub struct $id;
        impl CoreCrc for $id {
            type Register = $reg;
            const BITS: usize = $bits;
            const POLYNOMIAL: $reg = $poly;
            const INIT: $reg = $init;
            const REFLECTED: bool = $refout;
            const DATA_BIT_ORDER: $crate::crc::BitOrder = $bitord;
            const XOROUT: Self::Register = $xorout;

            fn crc_with<T>(crc: $reg, data: &[T]) -> $reg
                where $reg: From<T>, T: Copy + $crate::crc::ReverseBits
            {
                $crate::crc::$fun::<$bits, $reg, T>($poly, crc ^ $xorout, data) ^ $xorout
            }

            fn crc<T>(data: &[T]) -> Self::Register
                where Self::Register: From<T>, T: Copy + $crate::crc::ReverseBits
            {
                Self::crc_with($rinit ^ $xorout, data)
            }

            $(fn name() -> &'static str { $name })?

            $(fn validate() -> Self::Register {
                assert_ne!($bits, 0, "width must not be 0 in {:?}", Self);
                assert!($bits <= core::mem::size_of::<$reg>() * 8, "register too small for given width in {:?}", Self);
                const MASK: $reg = (1 << ($bits - 1))|((1 << ($bits - 1)) - 1);
                assert_eq!($poly & MASK, $poly, "too many bits in poly of {:?}", Self);
                assert_eq!($init & MASK, $init, "too many bits in init of {:?}", Self);
                assert_eq!($xorout & MASK, $xorout, "too many bits in xorout of {:?}", Self);
                assert_eq!($check & MASK, $check, "too many bits in check of {:?}", Self);
                assert_eq!(Self::crc(b"123456789"), $check, "{:?} check failed", Self);
                $check
            })?
        }
    };
}

pub use impl_crc;

macro_rules! bits {
    ($ty:ty) => { core::mem::size_of::<$ty>() * 8 };
}

pub trait OverflowingAdd: Sized {
    fn overflowing_add(self, rhs: Self) -> (Self, bool);
}

macro_rules! impl_overflowing_add {
    ($($ty:ty),*) => {
        $(impl OverflowingAdd for $ty {
            #[inline(always)]
            fn overflowing_add(self, rhs: Self) -> (Self, bool) {
                self.overflowing_add(rhs)
            }
        })*
    };
}

impl_overflowing_add!(u64, u32, u16, u8);

pub trait ReverseBits: Sized {
    fn reverse_bits(self) -> Self;
}

macro_rules! impl_reverse_bits {
    ($($ty:ty),*) => {
        $(impl ReverseBits for $ty {
            #[inline(always)]
            fn reverse_bits(self) -> Self {
                self.reverse_bits()
            }
        })*
    };
}

impl_reverse_bits!(u64, u32, u16, u8);

/// Continue CRC calculation. Return the calculated CRC value.
///
/// The result is right-aligned (towards LSB) if the width of the CRC register
/// is larger than `B`.
///
/// * `B` is the CRC algorithm bit width.
/// * `R` is the CRC register type, bit size of `R` mut be >= `B`.
/// * `T` is the data word type, bit size of `T` must be <= bit size `R`.
/// * `polynomial` is the CRC generator polynomial, the value must be
///   right-aligned if the width of the CRC register is larger than `B`.
/// * `crc` is the previous result of the CRC calculation or the INIT value
///   of the algorithm. The value should be right-aligned (towards LSB).
/// * `data` words from which to calculate CRC value. The CRC is calculated
///   starting from the most significant bit of each word.
pub fn crc<const B: usize, R, T>(polynomial: R, crc: R, data: &[T]) -> R
    where R: Copy +
             From<T> +
             BitXorAssign +
             OverflowingAdd +
             Shl<usize, Output=R> +
             Shr<usize, Output=R>,
          T: Copy
{
    assert_ne!(B, 0);
    assert!(B <= bits!(R));
    assert!(bits!(T) <= bits!(R));
    let mut crc = crc << (bits!(R) - B);
    let polynomial = polynomial << (bits!(R) - B);

    for dat in data.iter().copied() {
        crc ^= R::from(dat) << (bits!(R) - bits!(T));
        let mut carry;
        for _ in 0..bits!(T) {
            (crc, carry) = crc.overflowing_add(crc);
            if carry {
                crc ^= polynomial;
            }
        }
    }
    crc >> (bits!(R) - B)
}

/// Continue CRC calculation. Return the calculated CRC value.
///
/// The result is right-aligned (towards LSB) if the width of the CRC register
/// is larger than `B`.
///
/// * `B` is the CRC algorithm bit width.
/// * `R` is the CRC register type, bit size of `R` mut be >= `B`.
/// * `T` is the data word type, bit size of `T` must be <= bit size `R`.
/// * `polynomial` is the CRC generator polynomial, the value must be
///   right-aligned if the width of the CRC register is larger than `B`.
/// * `crc` is the previous result of the CRC calculation or the INIT value
///   of the algorithm. The value should be right-aligned (towards LSB).
/// * `data` words from which to calculate CRC value. The CRC is calculated
///   starting from the least significant bit of each word.
pub fn crc_refin<const B: usize, R, T>(polynomial: R, crc: R, data: &[T]) -> R
    where R: Copy +
             From<T> +
             BitXorAssign +
             OverflowingAdd +
             Shl<usize, Output=R> +
             Shr<usize, Output=R>,
          T: Copy + ReverseBits
{
    assert_ne!(B, 0);
    assert!(B <= bits!(R));
    assert!(bits!(T) <= bits!(R));
    let mut crc = crc << (bits!(R) - B);
    let polynomial = polynomial << (bits!(R) - B);

    for dat in data.iter().copied() {
        crc ^= R::from(dat.reverse_bits()) << (bits!(R) - bits!(T));
        let mut carry;
        for _ in 0..bits!(T) {
            (crc, carry) = crc.overflowing_add(crc);
            if carry {
                crc ^= polynomial;
            }
        }
    }
    crc >> (bits!(R) - B)
}

/// Continue CRC calculation. Return the calculated CRC value.
///
/// The result is reflected (bit-reversed) and right-aligned (towards LSB)
/// if the width of the CRC register is larger than `B`.
///
/// * `B` is the CRC algorithm bit width.
/// * `R` is the CRC register type, bit size of `R` mut be >= `B`.
/// * `T` is the data word type, bit size of `T` must be <= bit size `R`.
/// * `polynomial` is the CRC generator polynomial, the value must be
///   right-aligned if the width of the CRC register is larger than `B`.
/// * `crc` is the previous result of the CRC calculation or the reflected
///   INIT value of the algorithm. The value should be right-aligned (towards LSB).
/// * `data` words from which to calculate CRC value. The CRC is calculated
///   starting from the most significant bit of each word.
pub fn crc_refout<const B: usize, R, T>(polynomial: R, crc: R, data: &[T]) -> R
    where R: Copy +
             From<T> +
             BitXorAssign +
             OverflowingAdd +
             Shl<usize, Output=R> +
             Shr<usize, Output=R> +
             ReverseBits,
          T: Copy
{
    assert_ne!(B, 0);
    assert!(B <= bits!(R));
    assert!(bits!(T) <= bits!(R));
    let mut crc = crc.reverse_bits();
    let polynomial = polynomial << (bits!(R) - B);

    for dat in data.iter().copied() {
        crc ^= R::from(dat) << (bits!(R) - bits!(T));
        let mut carry;
        for _ in 0..bits!(T) {
            (crc, carry) = crc.overflowing_add(crc);
            if carry {
                crc ^= polynomial;
            }
        }
    }
    crc.reverse_bits()
}

/// Continue CRC calculation. Return the calculated CRC value.
///
/// The result is reflected (bit-reversed) and right-aligned (towards LSB)
/// if the width of the CRC register is larger than `B`.
///
/// * `B` is the CRC algorithm bit width.
/// * `R` is the CRC register type, bit size of `R` mut be >= `B`.
/// * `T` is the data word type, bit size of `T` must be <= bit size `R`.
/// * `polynomial` is the CRC generator polynomial, the value must be
///   right-aligned if the width of the CRC register is larger than `B`.
/// * `crc` is the previous result of the CRC calculation or the reflected
///   INIT value of the algorithm. The value should be right-aligned (towards LSB).
/// * `data` words from which to calculate CRC value. The CRC is calculated
///   starting from the least significant bit of each word.
pub fn crc_reflect<const B: usize, R, T>(polynomial: R, crc: R, data: &[T]) -> R
    where R: Copy +
             From<T> +
             BitXorAssign +
             OverflowingAdd +
             Shl<usize, Output=R> +
             Shr<usize, Output=R> +
             ReverseBits,
          T: Copy + ReverseBits
{
    assert_ne!(B, 0);
    assert!(B <= bits!(R));
    assert!(bits!(T) <= bits!(R));
    let mut crc = crc.reverse_bits();
    let polynomial = polynomial << (bits!(R) - B);

    for dat in data.iter().copied() {
        crc ^= R::from(dat.reverse_bits()) << (bits!(R) - bits!(T));
        let mut carry;
        for _ in 0..bits!(T) {
            (crc, carry) = crc.overflowing_add(crc);
            if carry {
                crc ^= polynomial;
            }
        }
    }
    crc.reverse_bits()
}

#[cfg(test)]
mod tests {
    use super::*;

    impl_crc!(MyCrc7{u8} width=7 poly=0x07 init=0x7f refin=true refout=true xorout=0x00 check=0x14);
    impl_crc!(MyCrc13{u32} width=13 poly=0x1111 init=0x1555 refin=true refout=false xorout=0x1fff check=0x19d2);
    impl_crc!(Crc5Usb{u8} width=5 poly=0x05 init=0x1f refin=true refout=true xorout=0x1f check=0x19 residue=0x06 name="CRC-5/USB");
    impl_crc!(Crc7Mmc{u8} width=7 poly=0x09 init=0x00 refin=false refout=false xorout=0x00 check=0x75 residue=0x00 name="CRC-7/MMC");
    impl_crc!(Crc7Rohc{u8} width=7 poly=0x4f init=0x7f refin=true refout=true xorout=0x00 check=0x53 residue=0x00 name="CRC-7/ROHC");
    impl_crc!(Crc7Umts{u8} width=7 poly=0x45 init=0x00 refin=false refout=false xorout=0x00 check=0x61 residue=0x00 name="CRC-7/UMTS");
    impl_crc!(Crc8I4321{u8} width=8 poly=0x07 init=0x00 refin=false refout=false xorout=0x55 check=0xa1 residue=0xac name="CRC-8/I-432-1");
    impl_crc!(Crc8Rohc{u8} width=8 poly=0x07 init=0xff refin=true refout=true xorout=0x00 check=0xd0 residue=0x00 name="CRC-8/ROHC");
    impl_crc!(Crc11Umts{u16} width=11 poly=0x307 init=0x000 refin=false refout=false xorout=0x000 check=0x061 residue=0x000 name="CRC-11/UMTS");
    impl_crc!(Crc12Umts{u16} width=12 poly=0x80f init=0x000 refin=false refout=true xorout=0x000 check=0xdaf residue=0x000 name="CRC-12/UMTS");
    impl_crc!(Crc16Umts{u16} width=16 poly=0x8005 init=0x0000 refin=false refout=false xorout=0x0000 check=0xfee8 residue=0x0000 name="CRC-16/UMTS");
    impl_crc!(Crc32Cksum{u32} width=32 poly=0x04c11db7 init=0x00000000 refin=false refout=false xorout=0xffffffff check=0x765e7680 residue=0xc704dd7b name="CRC-32/CKSUM");
    impl_crc!(Crc32Iscsi{u32} width=32 poly=0x1edc6f41 init=0xffffffff refin=true refout=true xorout=0xffffffff check=0xe3069283 residue=0xb798b438 name="CRC-32/ISCSI");
    impl_crc!(Crc32IsoHdlc{u32} width=32 poly=0x04c11db7 init=0xffffffff refin=true refout=true xorout=0xffffffff check=0xcbf43926 residue=0xdebb20e3 name="CRC-32/ISO-HDLC");
    impl_crc!(Crc32Jamcrc{u32} width=32 poly=0x04c11db7 init=0xffffffff refin=true refout=true xorout=0x00000000 check=0x340bc6d9 residue=0x00000000 name="CRC-32/JAMCRC");
    impl_crc!(Crc32Mef{u32} width=32 poly=0x741b8cd7 init=0xffffffff refin=true refout=true xorout=0x00000000 check=0xd2c22f51 residue=0x00000000 name="CRC-32/MEF");
    impl_crc!(Crc32Mpeg2{u32} width=32 poly=0x04c11db7 init=0xffffffff refin=false refout=false xorout=0x00000000 check=0x0376e6e7 residue=0x00000000 name="CRC-32/MPEG-2");
    impl_crc!(Crc32xfer{u32} width=32 poly=0x000000af init=0x00000000 refin=false refout=false xorout=0x00000000 check=0xbd0be338 residue=0x00000000 name="CRC-32/XFER");
    impl_crc!(Crc64Redis{u64} width=64 poly=0xad93d23594c935a9 init=0x0000000000000000 refin=true refout=true xorout=0x0000000000000000 check=0xe9c6d914c4b8d9ca residue=0x0000000000000000 name="CRC-64/REDIS");

    #[test]
    fn crc_works() {
        assert_eq!(MyCrc7::validate(), 0x14);
        assert_eq!(MyCrc13::validate(), 0x19d2);
        assert_eq!(Crc5Usb::validate(), 0x19);
        assert_eq!(Crc7Mmc::validate(), 0x75);
        assert_eq!(Crc7Rohc::validate(), 0x53);
        assert_eq!(Crc7Umts::validate(), 0x61);
        assert_eq!(Crc8I4321::validate(), 0xa1);
        assert_eq!(Crc8Rohc::validate(), 0xd0);
        assert_eq!(Crc11Umts::validate(), 0x061);
        assert_eq!(Crc12Umts::validate(), 0xdaf);
        assert_eq!(Crc16Umts::validate(), 0xfee8);
        assert_eq!(Crc32Cksum::validate(), 0x765e7680);
        assert_eq!(Crc32Iscsi::validate(), 0xe3069283);
        assert_eq!(Crc32IsoHdlc::validate(), 0xcbf43926);
        assert_eq!(Crc32Jamcrc::validate(), 0x340bc6d9);
        assert_eq!(Crc32Mef::validate(), 0xd2c22f51);
        assert_eq!(Crc32Mpeg2::validate(), 0x0376e6e7);
        assert_eq!(Crc32xfer::validate(), 0xbd0be338);
        assert_eq!(Crc64Redis::validate(), 0xe9c6d914c4b8d9ca);

        assert_eq!(Crc5Usb::name(), "CRC-5/USB");
        assert_eq!(Crc7Mmc::name(), "CRC-7/MMC");
        assert_eq!(Crc7Rohc::name(), "CRC-7/ROHC");
        assert_eq!(Crc7Umts::name(), "CRC-7/UMTS");
        assert_eq!(Crc8I4321::name(), "CRC-8/I-432-1");
        assert_eq!(Crc8Rohc::name(), "CRC-8/ROHC");
        assert_eq!(Crc11Umts::name(), "CRC-11/UMTS");
        assert_eq!(Crc12Umts::name(), "CRC-12/UMTS");
        assert_eq!(Crc16Umts::name(), "CRC-16/UMTS");
        assert_eq!(Crc32Cksum::name(), "CRC-32/CKSUM");
        assert_eq!(Crc32Iscsi::name(), "CRC-32/ISCSI");
        assert_eq!(Crc32IsoHdlc::name(), "CRC-32/ISO-HDLC");
        assert_eq!(Crc32Jamcrc::name(), "CRC-32/JAMCRC");
        assert_eq!(Crc32Mef::name(), "CRC-32/MEF");
        assert_eq!(Crc32Mpeg2::name(), "CRC-32/MPEG-2");
        assert_eq!(Crc32xfer::name(), "CRC-32/XFER");
        assert_eq!(Crc64Redis::name(), "CRC-64/REDIS");
    }
}
