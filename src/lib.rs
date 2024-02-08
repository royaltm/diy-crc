#![cfg_attr(not(test), no_std)]

pub mod crc;

pub use crc::*;

#[cfg(test)]
mod tests {
    use super::*;
    impl_crc!(MyCrc7{u8}
      width=7 poly=0x07 init=0x7f refin=true refout=true xorout=0x00 check=0x14);

    impl_crc!(Crc5Usb{u8}
      width=5 poly=0x05 init=0x1f refin=true refout=true xorout=0x1f check=0x19 residue=0x06 name="CRC-5/USB");

    impl_crc!(Crc8Rohc{u8}
      width=8 poly=0x07 init=0xff refin=true refout=true xorout=0x00 check=0xd0 residue=0x00 name="CRC-8/ROHC");

    impl_crc!(Crc11Umts{u16}
      width=11 poly=0x307 init=0x000 refin=false refout=false xorout=0x000 check=0x061 residue=0x000 name="CRC-11/UMTS");

    impl_crc!(Crc32Cksum{u32}
      width=32 poly=0x04c11db7 init=0x00000000 refin=false refout=false xorout=0xffffffff check=0x765e7680 residue=0xc704dd7b name="CRC-32/CKSUM");

    impl_crc!(Crc32Mpeg2{u32}
      width=32 poly=0x04c11db7 init=0xffffffff refin=false refout=false xorout=0x00000000 check=0x0376e6e7 residue=0x00000000 name="CRC-32/MPEG-2");

    impl_crc!(Crc64Redis{u64}
      width=64 poly=0xad93d23594c935a9 init=0x0000000000000000 refin=true refout=true xorout=0x0000000000000000 check=0xe9c6d914c4b8d9ca residue=0x0000000000000000 name="CRC-64/REDIS");

   #[test]
    fn crc_readme() {
        assert_eq!(MyCrc7::validate(), 0x14);
        assert_eq!(MyCrc7::crc(b"123456789"), 0x14);
        let crc = MyCrc7::crc::<u8>(&[]);
        let crc = MyCrc7::crc_with(crc, b"12345");
        let crc = MyCrc7::crc_with(crc, b"678");
        assert_eq!(MyCrc7::crc_with(crc, b"9"), 0x14);

        assert_eq!(Crc5Usb::name(), "CRC-5/USB");
        // Larger than byte character sizes:
        let data = [0xdeadbacau32, 0x12345678, 0xffffffff];
        let s = format!("{}: 0x{:x}", Crc32Cksum, Crc32Cksum::crc(&data));
        assert_eq!(s, "CRC-32/CKSUM: 0xc0ebf59b");
        let s = format!("{}: 0x{:x}", Crc64Redis, Crc64Redis::crc(&data));
        assert_eq!(s, "CRC-64/REDIS: 0x9fd65b8ef4886386");
    }
}
