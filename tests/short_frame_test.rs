use rtmt::short_frame_decode::NcDecode;
use rtmt::short_frame_encode::NcEncode;
use std::option::Option;

fn valid(de_in: &[i8], de_expected: &[i8]) {
    println!("de_in {:?}", de_in);
    let mut de = NcDecode::new();
    for d in &de_in[..de_in.len() - 1] {
        de.decode(*d);
    }

    de.clear_out();
    // let _ = de.decode(de_in[de_in.len() - 1]);
    assert_eq!(de.decode(de_in[de_in.len() - 1]), Option::Some(-1i32));
    assert_eq!(de.out_buf, de_expected);
    println!("frame {:?}", de.out_buf);
}

fn frame(en: &mut NcEncode, data: &[i8]) -> Vec<i8> {
    let mut v: Vec<i8> = vec![];
    en.frame_begin();

    for d in data {
        v.append(&mut en.encode(*d))
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
    s.append(&mut en.encode(65));

    en.frame_begin();
    s.append(&mut en.encode(97));
    s.append(&mut en.frame_end());

    s.append(&mut en.encode(66));
    s.append(&mut en.frame_end());

    valid(&s, &[65, 66]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A_B_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    en.frame_begin();
    s.append(&mut en.encode(65));

    en.frame_begin();
    s.append(&mut en.frame_end());

    s.append(&mut en.encode(66));
    s.append(&mut en.frame_end());

    valid(&s, &[65, 66]);
}

#[test]
#[allow(non_snake_case)]
fn encode_00_0_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    en.frame_begin();
    s.append(&mut en.encode(0));

    en.frame_begin();
    s.append(&mut en.encode(0));
    s.append(&mut en.frame_end());

    s.append(&mut en.encode(0));
    s.append(&mut en.frame_end());

    valid(&s, &[0, 0]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A__B_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    en.frame_begin();
    s.append(&mut en.encode(65));

    en.frame_begin();

    en.frame_begin();
    s.append(&mut en.frame_end());

    s.append(&mut en.frame_end());

    s.append(&mut en.encode(66));
    s.append(&mut en.frame_end());

    valid(&s, &[65, 66]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A_0_0_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    en.frame_begin();
    s.append(&mut en.encode(65));

    en.frame_begin();
    s.append(&mut en.encode(0));
    s.append(&mut en.frame_end());

    s.append(&mut en.encode(0));
    s.append(&mut en.frame_end());

    valid(&s, &[65, 0]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A00_0_0_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    en.frame_begin();
    s.append(&mut en.encode(65));

    en.frame_begin();
    s.append(&mut en.encode(0));
    s.append(&mut en.frame_end());

    s.append(&mut en.encode(0));

    en.frame_begin();
    s.append(&mut en.encode(0));
    s.append(&mut en.frame_end());

    s.append(&mut en.encode(0));
    s.append(&mut en.frame_end());

    valid(&s, &[65, 0, 0]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A0_0_a_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    en.frame_begin();
    s.append(&mut en.encode(65));

    en.frame_begin();
    s.append(&mut en.encode(0));

    en.frame_begin();
    s.append(&mut en.encode(97));
    s.append(&mut en.frame_end());

    s.append(&mut en.frame_end());

    s.append(&mut en.frame_end());

    valid(&s, &[65]);
}

#[test]
#[allow(non_snake_case)]
fn encode_AD_B_C_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    en.frame_begin();
    s.append(&mut en.encode(65));

    en.frame_begin();
    s.append(&mut en.encode(66));

    en.frame_begin();
    s.append(&mut en.encode(67));
    s.append(&mut en.frame_end());

    s.append(&mut en.frame_end());

    s.append(&mut en.encode(68));

    s.append(&mut en.frame_end());

    valid(&s, &[65, 68])
}

#[test]
#[allow(non_snake_case)]
fn encode_longest_short_frame() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    let mut v = vec![];
    en.frame_begin();

    for i in 1..128 {
        s.append(&mut en.encode(i as i8));
        v.push(i as i8);
    }

    s.append(&mut en.frame_end());

    valid(&s, &v)
}

#[test]
#[allow(non_snake_case)]
fn encode_longest_short_frame_0_begin() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    let mut v = vec![];
    en.frame_begin();

    for i in 0..127 {
        s.append(&mut en.encode(i as i8));
        v.push(i as i8);
    }

    s.append(&mut en.frame_end());

    valid(&s, &v)
}

#[test]
#[allow(non_snake_case)]
fn encode_longest_short_frame_0_end() {
    let mut en = NcEncode::new();
    let mut s = vec![];
    let mut v = vec![];
    en.frame_begin();

    for i in 1..127 {
        s.append(&mut en.encode(i as i8));
        v.push(i as i8);
    }

    s.append(&mut en.encode(0));
    v.push(0);

    s.append(&mut en.frame_end());

    valid(&s, &v)
}
