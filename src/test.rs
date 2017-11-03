#![allow(dead_code)]

use std::result;
use std::fs;
use std::f64;
use ::*;
use conversions::*;

#[test] fn test() {
    let mut writer = BitWriter::new_with_precision(fs::File::create("/home/scott/Desktop/test.txt").expect("file not created"), Precision::Bit);
    let str_mask = StringConverter::NullTerminated;
    let str_mask_2 = StringConverter::FixedLength { length: 8 };
    let str_mask_3 = StringConverter::LengthPrefixed { prefix_bits: 4 };
    let str_mask_4 = StringConverter::default();
    let mask = BitMask::bits(17);
    writer.write(&mask).expect("mask not written");
    writer.write_using(&(u16::max_value() as u32), &mask).expect("data not written");
    writer.write(&str_mask).expect("string mask not written");
    writer.write(&str_mask_2).expect("string 2 mask not written");
    writer.write(&str_mask_3).expect("string 3 mask not written");
    writer.write(&str_mask_4).expect("string 4 mask not written");
    writer.write_using(&"Long test message for testing reasons and testing.".to_owned(), &str_mask).expect("string 1 not written");
    writer.write_using(&String::from("test\02"), &str_mask_2).expect("string 2 not written");
    writer.write_using(&"0123456789 test".to_owned(), &str_mask_3).expect("string 3 not written");
    writer.write(&"This is a test message. Hopefully it works.".to_owned()).expect("string 4 not written");
    writer.write(&Some(f64::consts::PI*2.0)).unwrap();
    writer.write::<Option<u32>>(&None).unwrap();
    writer.write::<result::Result<i8, bool>>(&Ok(-17)).unwrap();
    writer.write::<result::Result<u32, bool>>(&Err(true)).unwrap();
    writer.close().expect("stream not closed");
    let mut reader = BitReader::new_with_precision(fs::File::open("/home/scott/Desktop/test.txt").expect("file not opened"), Precision::Bit);
    let mask: BitMask = reader.read().expect("invalid mask");
    println!("{:?} => {:?}", mask, reader.read_using::<u64, _>(&mask));
    let str_mask: StringConverter = reader.read().expect("invalid string mask");
    let str_mask_2: StringConverter = reader.read().expect("invalid string 2 mask");
    let str_mask_3: StringConverter = reader.read().expect("invalid string 3 mask");
    let str_mask_4: StringConverter = reader.read().expect("invalid string 4 mask");
    println!("{:?} => {:?}", str_mask, reader.read_using(&str_mask));
    println!("{:?} => {:?}", str_mask_2, reader.read_using(&str_mask_2));
    println!("{:?} => {:?}", str_mask_3, reader.read_using(&str_mask_3));
    println!("{:?} => {:?}", str_mask_4, reader.read_using(&str_mask_4));
    println!("{:?}", reader.read::<Option<f64>>());
    println!("{:?}", reader.read::<Option<u32>>());
    println!("{:?}", reader.read::<result::Result<i8, bool>>());
    println!("{:?}", reader.read::<result::Result<u32, bool>>());
    assert!(reader.read_bit().is_err(), "stream read error");
}