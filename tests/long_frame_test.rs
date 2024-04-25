use rtmt::decode::NcDecode;
use rtmt::long_frame_encode::NcEncode;

fn valid(de_in: &[i8], de_expected: &[i8]) {
    println!("de_in {:?}\n", de_in);
    println!("de_in {:x?}\n", de_in);

    let mut de = NcDecode::new();
    for d in &de_in[..de_in.len() - 1] {
        de.decode(*d);
    }

    de.clear_out();
    let _ = de.decode(de_in[de_in.len() - 1]);
    // assert_eq!(de.decode(de_in[de_in.len() - 1]), Option::Some(-1i32));
    println!("frame {:?}", de.out_buf);
    assert_eq!(de.out_buf, de_expected);
}

#[test]
#[allow(non_snake_case)]
fn encode_ABC() {
    let mut en = NcEncode::new();
    let s = en.encode_frame(&[65, 66, 67]);
    valid(&s, &[65, 66, 67]);
}

#[test]
#[allow(non_snake_case)]
fn encode_0() {
    let mut en = NcEncode::new();
    let s = en.encode_frame(&[0]);

    valid(&s, &[0]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A0() {
    let mut en = NcEncode::new();
    let s = en.encode_frame(&[65, 0]);

    valid(&s, &[65, 0]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A00B0() {
    let mut en = NcEncode::new();
    let s = en.encode_frame(&[65, 0, 0, 66, 0]);

    valid(&s, &[65, 0, 0, 66, 0]);
}

#[test]
#[allow(non_snake_case)]
fn encode_A_a_B_preempt() {
    let mut en = NcEncode::new();
    let mut s = vec![];

    en.frame_begin(2);
    s.append(&mut en.encode(65));

    en.frame_begin(1);
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
    en.frame_begin(2);
    s.append(&mut en.encode(65));

    en.frame_begin(1);
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
    en.frame_begin(2);
    s.append(&mut en.encode(0));

    en.frame_begin(1);
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
    en.frame_begin(2);
    s.append(&mut en.encode(65));

    en.frame_begin(0);

    en.frame_begin(0);
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
    en.frame_begin(2);
    s.append(&mut en.encode(65));

    en.frame_begin(0);
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
    en.frame_begin(3);
    s.append(&mut en.encode(65));

    en.frame_begin(1);
    s.append(&mut en.encode(0));
    s.append(&mut en.frame_end());

    s.append(&mut en.encode(0));

    en.frame_begin(1);
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
    en.frame_begin(1);
    s.append(&mut en.encode(65));

    en.frame_begin(1);
    s.append(&mut en.encode(0));

    en.frame_begin(1);
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
    en.frame_begin(2);
    s.append(&mut en.encode(65));

    en.frame_begin(1);
    s.append(&mut en.encode(66));

    en.frame_begin(1);
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
    en.frame_begin(127);

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
    let mut v = vec![];

    for i in 0..127 {
        v.push(i as i8);
    }

    let s = en.encode_frame(&v);
    valid(&s, &v)
}

#[test]
#[allow(non_snake_case)]
fn encode_longest_short_frame_0_end() {
    let mut en = NcEncode::new();
    let mut v = vec![];

    for i in 1..127 {
        v.push(i as i8);
    }

    v.push(0);
    let s = en.encode_frame(&v);

    valid(&s, &v)
}

#[test]
#[allow(non_snake_case)]
fn encode_minimal_long_frame() {
    let mut en = NcEncode::new();
    let mut v = vec![];

    for i in 1..129 {
        v.push(i as i8);
    }

    let s = en.encode_frame(&v);
    valid(&s, &v)
}

#[test]
#[allow(non_snake_case)]
fn encode_0_minimal_long_frame_0() {
    let mut en = NcEncode::new();
    let mut v = vec![];

    v.push(0);
    for i in 1..128 {
        v.push(i as i8);
    }

    let s = en.encode_frame(&v);
    valid(&s, &v)
}
