use rtmt::decode::NcDecode;
use rtmt::encode::NcEncode;

fn valid(de_in: &[i8], de_expected: &[i8]) {
    println!("de_in {:?}", de_in);
    let mut de = NcDecode::new();
    for d in &de_in[..de_in.len() - 1] {
        de.decode(*d);
    }

    de.clear();
    de.decode(de_in[de_in.len() - 1]);

    assert_eq!(de.out_buf, de_expected);
    println!("frame {:?}", de.out_buf);
}

fn frame(en: &mut NcEncode, data: &[i8]) -> Vec<i8> {
    let mut v: Vec<i8> = vec![];
    en.frame_begin();

    for d in data {
        v.push(en.encode(*d))
    }

    v.append(&mut en.frame_end());
    v
}

#[test]
#[allow(non_snake_case)]
fn encode_ABC() {
    let mut en = NcEncode::new();
    let s = frame(&mut en, &[65, 66, 67]);
    valid(&s, &[65, 66, 67]);
}

#[test]
#[allow(non_snake_case)]
fn encode_0() {
    let mut en = NcEncode::new();
    let s = frame(&mut en, &[0]);

    valid(&s, &[0]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A0() {
    let mut en = NcEncode::new();
    let s = frame(&mut en, &[65, 0]);

    valid(&s, &[65, 0]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A00B0() {
    let mut en = NcEncode::new();
    let s = frame(&mut en, &[65, 0, 0, 66, 0]);

    valid(&s, &[65, 0, 0, 66, 0]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A_a_B_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];

    en.frame_begin();
    s.push(en.encode(65));

    en.frame_begin();
    s.push(en.encode(97));
    s.append(&mut en.frame_end());

    s.push(en.encode(66));
    s.append(&mut en.frame_end());

    valid(&s, &[65, 66]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A_B_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    en.frame_begin();
    s.push(en.encode(65));

    en.frame_begin();
    s.append(&mut en.frame_end());

    s.push(en.encode(66));
    s.append(&mut en.frame_end());

    valid(&s, &[65, 66]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A__B_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    en.frame_begin();
    s.push(en.encode(65));

    en.frame_begin();

    en.frame_begin();
    s.append(&mut en.frame_end());

    s.append(&mut en.frame_end());

    s.push(en.encode(66));
    s.append(&mut en.frame_end());

    valid(&s, &[65, 66]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A_0_0_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    en.frame_begin();
    s.push(en.encode(65));

    en.frame_begin();
    s.push(en.encode(0));
    s.append(&mut en.frame_end());

    s.push(en.encode(0));
    s.append(&mut en.frame_end());

    valid(&s, &[65, 0]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A00_0_0_preempt() {
    let mut nc = NcEncode::new();
    let mut s = vec![];
    nc.frame_begin();
    s.push(nc.encode(65));

    nc.frame_begin();
    s.push(nc.encode(0));
    s.append(&mut nc.frame_end());

    s.push(nc.encode(0));

    nc.frame_begin();
    s.push(nc.encode(0));
    s.append(&mut nc.frame_end());

    s.push(nc.encode(0));
    s.append(&mut nc.frame_end());

    valid(&s, &[65, 0, 0]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A0_0_a_preempt() {
    let mut nc = NcEncode::new();
    let mut s = vec![];
    nc.frame_begin();
    s.push(nc.encode(65));

    nc.frame_begin();
    s.push(nc.encode(0));

    nc.frame_begin();
    s.push(nc.encode(97));
    s.append(&mut nc.frame_end());

    s.append(&mut nc.frame_end());

    s.append(&mut nc.frame_end());
    println!("s {:?}", s);

    valid(&s, &[65]);
}

#[test]
#[allow(non_snake_case)]
fn encode_AD_B_C_preempt() {
    let mut nc = NcEncode::new();
    let mut s = vec![];
    nc.frame_begin();
    s.push(nc.encode(65));

    nc.frame_begin();
    s.push(nc.encode(66));

    nc.frame_begin();
    s.push(nc.encode(67));
    s.append(&mut nc.frame_end());

    s.append(&mut nc.frame_end());

    s.push(nc.encode(68));

    s.append(&mut nc.frame_end());

    valid(&s, &[65, 68])
}

// assert_eq!(s, [65, 1, 97, 2, 0, -1, 0, 2, -1, 0].as_slice())

// #[test]
// #[allow(non_snake_case)]
// fn encode_long_preempt() {
//     let mut nc = NcEncode::new();
//     let mut s = vec![];
//     let mut v = vec![];
//     nc.frame_begin();

//     for i in 0..7 {
//         s.append(&mut nc.encode(65 + i));
//         v.push(65 + i);
//     }
//     s.append(&mut nc.frame_end());
//     println!("s {:?}", s);

//     let mut de = NcDecode::new();
//     for d in s {
//         de.decode(d as u8);
//     }

//     // assert_eq!(de.out_buf, [65u8, 66, 67].as_slice());
//     println!("frame {:?}", de.out_buf);
// }
