//

use std::collections::VecDeque;

#[derive(Debug)]
struct Nc {
    in_buf: Vec<u8>,
    out_buf: VecDeque<u8>,
}

impl Nc {
    pub fn new() -> Self {
        Nc {
            in_buf: Vec::new(),
            out_buf: VecDeque::new(),
        }
    }

    pub fn clear(&mut self) {
        self.out_buf = VecDeque::new();
    }

    pub fn scan_pkg(&mut self, p: usize, skip: bool) -> usize {
        let offset = self.in_buf[p] as i8;
        let mut offset_end = offset > 0;
        let mut offset_abs: usize = offset.unsigned_abs() as usize;
        let mut i: usize = 1; // skip length
        loop {
            if offset_end && i == offset_abs {
                return i;
            }
            let data = self.in_buf[p - i];
            if data == 0 {
                println!("preemption package at i {}", i);
                i = 1 + i + self.scan_pkg(p - i - 1, true);
                println!("continue at i {}", i);
                continue;
            }
            println!("i {}, d {}, offset_abs {}", i, data, offset_abs);

            if i == offset_abs && !offset_end {
                println!("replace sentinel");
                if !skip {
                    self.out_buf.push_front(0);
                }
                let offset = data as i8;
                offset_end = offset > 0;
                offset_abs += offset.unsigned_abs() as usize;
                i += 1; // skip length
            } else {
                if !skip {
                    self.out_buf.push_front(data);
                }
                i += 1;
            }
        }
    }

    pub fn decode(&mut self, data: u8) -> bool {
        let nc = self;
        println!("data {}", data);
        nc.in_buf.push(data);

        if data == 0 {
            println!("in_buf {:?}", nc.in_buf);
            nc.scan_pkg(nc.in_buf.len() - 2, false);
            true
        } else {
            false
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
        assert!(!nc.decode(65));
        assert!(!nc.decode(66));
        assert!(!nc.decode(67));
        assert!(!nc.decode(4)); // length
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65u8, 66, 67].as_slice());
        println!("pkg {:?}", nc.out_buf);
        let s: Vec<u8> = nc.out_buf.into();
        println!("s {}", std::str::from_utf8(&s).unwrap());
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_0() {
        let mut nc = Nc::new();
        assert!(!nc.decode(1));
        assert!(!nc.decode(-1i8 as u8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0].as_slice());
        println!("pkg {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_00() {
        let mut nc = Nc::new();
        assert!(!nc.decode(1));
        assert!(!nc.decode(-1i8 as u8));
        assert!(!nc.decode(-1i8 as u8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0, 0].as_slice());
        println!("pkg {:?}", nc.out_buf);
    }
    #[test]
    #[allow(non_snake_case)]
    fn decode_A0() {
        let mut nc = Nc::new();
        assert!(!nc.decode(65));
        assert!(!nc.decode(2));
        assert!(!nc.decode(-1i8 as u8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65, 0].as_slice());
        println!("pkg {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_A00B0() {
        let mut nc = Nc::new();
        assert!(!nc.decode(65));
        assert!(!nc.decode(2));
        assert!(!nc.decode(-1i8 as u8));
        assert!(!nc.decode(66));
        assert!(!nc.decode(-2i8 as u8));
        assert!(!nc.decode(-1i8 as u8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65, 0, 0, 66, 0].as_slice());
        println!("pkg {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_AaB_preempt() {
        let mut nc = Nc::new();
        assert!(!nc.decode(65));
        assert!(!nc.decode(97));
        assert!(!nc.decode(2));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [97].as_slice());
        println!("pkg {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(66));
        assert!(!nc.decode(6));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65, 66].as_slice());
        println!("pkg {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_AB_preempt() {
        let mut nc = Nc::new();
        assert!(!nc.decode(65));

        assert!(!nc.decode(1));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [].as_slice());
        println!("pkg {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(66));
        assert!(!nc.decode(5));
        assert!(nc.decode(0)); // sentinel

        assert_eq!(nc.out_buf, [65, 66].as_slice());
        println!("pkg {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_A00_preempt() {
        let mut nc = Nc::new();
        assert!(!nc.decode(65));

        assert!(!nc.decode(1));
        assert!(!nc.decode(-1i8 as u8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0].as_slice());
        println!("pkg {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(5));
        assert!(!nc.decode(-1i8 as u8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65, 0].as_slice());
        println!("pkg {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_A00_0_0_preempt() {
        let mut nc = Nc::new();
        assert!(!nc.decode(65));

        assert!(!nc.decode(1));
        assert!(!nc.decode(-1i8 as u8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0].as_slice());
        println!("pkg {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(5));

        assert!(!nc.decode(1));
        assert!(!nc.decode(-1i8 as u8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0].as_slice());
        println!("pkg {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(-4i8 as u8));
        assert!(!nc.decode(-1i8 as u8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65, 0, 0].as_slice());
        println!("pkg {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_A0_0_a_preempt() {
        let mut nc = Nc::new();
        assert!(!nc.decode(65));

        assert!(!nc.decode(1));

        assert!(!nc.decode(97));
        assert!(!nc.decode(2));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [97].as_slice());
        println!("pkg {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(-4i8 as u8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0].as_slice());
        println!("pkg {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(8));
        assert!(!nc.decode(-1i8 as u8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65, 0].as_slice());
        println!("pkg {:?}", nc.out_buf);
    }
}
