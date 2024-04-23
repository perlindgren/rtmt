use rtmt::decode::NcDecode;
use rtmt::encode::NcEncode;

#[test]
#[allow(non_snake_case)]
fn encode_ABC() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    en.frame_begin();

    s.append(&mut en.encode(65));
    s.append(&mut en.encode(66));
    s.append(&mut en.encode(67));

    s.append(&mut en.frame_end());
    println!("s {:?}", s);
    assert_eq!(s, [65, 66, 67, 4, 0].as_slice());

    let mut de = NcDecode::new();
    for d in s {
        de.decode(d as u8);
    }

    assert_eq!(de.out_buf, [65u8, 66, 67].as_slice());
    println!("frame {:?}", de.out_buf);
}

#[test]
#[allow(non_snake_case)]
fn encode_long_preempt() {
    let mut nc = NcEncode::new();
    let mut s = vec![];
    let mut v = vec![];
    nc.frame_begin();

    for i in 0..7 {
        s.append(&mut nc.encode(65 + i));
        v.push(65 + i);
    }
    s.append(&mut nc.frame_end());
    println!("s {:?}", s);

    let mut de = NcDecode::new();
    for d in s {
        de.decode(d as u8);
    }

    // assert_eq!(de.out_buf, [65u8, 66, 67].as_slice());
    println!("frame {:?}", de.out_buf);
}
