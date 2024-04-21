//

use std::{borrow::BorrowMut, cell::RefCell};

const MAX_LEVEL: usize = 4;
const MAX_PKG_SIZE: usize = 256;
const SIZE: usize = MAX_LEVEL * MAX_PKG_SIZE;

#[derive(Debug)]
struct Nc {
    ptr: usize,
    in_buf: [u8; SIZE],
    out_buf: [u8; MAX_PKG_SIZE],
}

impl Nc {
    pub fn new() -> Self {
        Nc {
            ptr: 0,
            in_buf: [0; SIZE],
            out_buf: [0; MAX_PKG_SIZE],
        }
    }

    pub fn decode(&mut self, data: u8) -> Option<&[u8]> {
        let nc = self;
        println!("data {}", data);
        nc.in_buf[nc.ptr] = data;
        nc.ptr = (nc.ptr + 1) % SIZE;

        if data == 0 {
            let mut skip = false;
            let pkg_size = nc.in_buf[(SIZE + nc.ptr - 2) % SIZE];
            println!("pkg_size {}", pkg_size);
            let mut i = 0;
            while i < pkg_size {
                let d = nc.in_buf[(SIZE - 3 + nc.ptr - i as usize) % SIZE];
                println!("i {} d {}", i, d);
                if skip {
                    if d == 0 {
                        println!("end skip");
                        skip = false;
                    } else {
                        println!("skip {}", d);
                        i += d;
                        continue;
                    }
                } else if d == 0 {
                    println!("start skip");
                    skip = true;
                } else {
                    nc.out_buf[(pkg_size - 1 - i) as usize] = d;
                }
                i += 1;
            }
            Some(&nc.out_buf[0..pkg_size as usize])
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[allow(non_snake_case)]
    fn decode_ABC() {
        let mut nc = Nc::new();
        assert_eq!(nc.decode(65), None);
        assert_eq!(nc.decode(66), None);
        assert_eq!(nc.decode(67), None);
        assert_eq!(nc.decode(3), None); // length
        let s = nc.decode(0).unwrap();
        assert_eq!(s, [65u8, 66, 67].as_slice());
        println!("s {}", std::str::from_utf8(s).unwrap());
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_Aa() {
        let mut nc = Nc::new();
        assert_eq!(nc.decode(65), None);
        assert_eq!(nc.decode(97), None);
        assert_eq!(nc.decode(1), None); // length
        let s = nc.decode(0).unwrap();
        println!("s {}", std::str::from_utf8(s).unwrap());
    }
    #[test]
    #[allow(non_snake_case)]
    fn decode_AaB() {
        let mut nc = Nc::new();

        assert_eq!(nc.decode(65), None);
        assert_eq!(nc.decode(97), None);
        assert_eq!(nc.decode(1), None); // length
        let s = nc.decode(0).unwrap();
        println!("s {}", std::str::from_utf8(s).unwrap());
        assert_eq!(nc.decode(66), None);
        assert_eq!(nc.decode(5), None); // length
        let s = nc.decode(0).unwrap();
        println!("s {}", std::str::from_utf8(s).unwrap());
    }
}
