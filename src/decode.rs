//

use std::collections::VecDeque;

#[derive(Debug, Default)]
pub struct NcDecode {
    in_buf: Vec<i8>,
    out_buf: VecDeque<i8>,
}

impl NcDecode {
    // new decoder
    pub fn new() -> Self {
        NcDecode {
            in_buf: Vec::new(),
            out_buf: VecDeque::new(),
        }
    }

    // clear output
    pub fn clear(&mut self) {
        self.out_buf = VecDeque::new();
    }

    // scan frame recursively
    pub fn scan_frame(&mut self, mut p: usize, skip: bool) -> usize {
        println!("scan_frame p {}, skip {}", p, skip);
        let offset = self.in_buf[p];
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
                p = self.scan_frame(p - i - 1, true);
                println!(
                    "continue at i {}, p {}, offset_abs {}, p - i = {}",
                    i,
                    p,
                    offset_abs,
                    p - i
                );
                continue;
            }
            println!("i {}, d {}, offset_abs {}", i, data, offset_abs);

            if i == offset_abs && !offset_end {
                if !skip {
                    println!("replace sentinel");
                    self.out_buf.push_front(0);
                }
                offset_end = data > 0;
                offset_abs += data.unsigned_abs() as usize;
            } else if !skip {
                self.out_buf.push_front(data);
            }
            i += 1;
        }
    }

    pub fn decode(&mut self, data: i8) -> bool {
        let nc = self;
        println!("data {}", data);
        nc.in_buf.push(data);

        if data == 0 {
            println!("in_buf {:?}", nc.in_buf);
            nc.scan_frame(nc.in_buf.len() - 2, false);
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
        let mut nc = NcDecode::new();
        assert!(!nc.decode(65));
        assert!(!nc.decode(66));
        assert!(!nc.decode(67));
        assert!(!nc.decode(4)); // length
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65i8, 66, 67].as_slice());
        println!("frame {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_0() {
        let mut nc = NcDecode::new();
        assert!(!nc.decode(1));
        assert!(!nc.decode(-1i8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0].as_slice());
        println!("frame {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_00() {
        let mut nc = NcDecode::new();
        assert!(!nc.decode(1));
        assert!(!nc.decode(-1i8));
        assert!(!nc.decode(-1i8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0, 0].as_slice());
        println!("frame {:?}", nc.out_buf);
    }
    #[test]
    #[allow(non_snake_case)]
    fn decode_A0() {
        let mut nc = NcDecode::new();
        assert!(!nc.decode(65));
        assert!(!nc.decode(2));
        assert!(!nc.decode(-1i8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65, 0].as_slice());
        println!("frame {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_A00B0() {
        let mut nc = NcDecode::new();
        assert!(!nc.decode(65));
        assert!(!nc.decode(2));
        assert!(!nc.decode(-1i8));
        assert!(!nc.decode(66));
        assert!(!nc.decode(-2i8));
        assert!(!nc.decode(-1i8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65, 0, 0, 66, 0].as_slice());
        println!("frame {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_AaB_preempt() {
        let mut nc = NcDecode::new();
        assert!(!nc.decode(65));
        assert!(!nc.decode(97));
        assert!(!nc.decode(2));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [97].as_slice());
        println!("frame {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(66));
        assert!(!nc.decode(3));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65, 66].as_slice());
        println!("frame {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_AB_preempt() {
        let mut nc = NcDecode::new();
        assert!(!nc.decode(65));

        assert!(!nc.decode(1));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [].as_slice());
        println!("frame {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(66));
        assert!(!nc.decode(3));
        assert!(nc.decode(0)); // sentinel

        assert_eq!(nc.out_buf, [65, 66].as_slice());
        println!("frame {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_A00_preempt() {
        let mut nc = NcDecode::new();
        assert!(!nc.decode(65));

        assert!(!nc.decode(1));
        assert!(!nc.decode(-1i8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0].as_slice());
        println!("frame {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(2));
        assert!(!nc.decode(-1i8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65, 0].as_slice());
        println!("frame {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_A00_0_0_preempt() {
        let mut nc = NcDecode::new();
        assert!(!nc.decode(65));

        assert!(!nc.decode(1));
        assert!(!nc.decode(-1i8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0].as_slice());
        println!("frame {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(2));

        assert!(!nc.decode(1));
        assert!(!nc.decode(-1i8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0].as_slice());
        println!("frame {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(-1i8));
        assert!(!nc.decode(-1i8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [65, 0, 0].as_slice());
        println!("frame {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_A0_0_a_preempt() {
        let mut nc = NcDecode::new();
        assert!(!nc.decode(65));

        assert!(!nc.decode(1));

        assert!(!nc.decode(97));
        assert!(!nc.decode(2));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [97].as_slice());
        println!("frame {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(-1i8));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [0].as_slice());
        println!("frame {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(2));
        assert!(!nc.decode(-1i8));
        assert!(nc.decode(0)); // sentinel
                               // assert_eq!(nc.out_buf, [65, 0].as_slice());
        println!("frame {:?}", nc.out_buf);
    }

    #[test]
    #[allow(non_snake_case)]
    fn decode_AD_B_C_preempt() {
        let mut nc = NcDecode::new();
        assert!(!nc.decode(65));

        assert!(!nc.decode(66));

        assert!(!nc.decode(67));
        assert!(!nc.decode(2));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [67].as_slice());
        println!("frame {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(2));
        assert!(nc.decode(0)); // sentinel
        assert_eq!(nc.out_buf, [66].as_slice());
        println!("frame {:?}", nc.out_buf);
        nc.clear();

        assert!(!nc.decode(68));
        assert!(!nc.decode(3));
        assert!(nc.decode(0)); // sentinel
                               // assert_eq!(nc.out_buf, [65, 0].as_slice());
        println!("frame {:?}", nc.out_buf);
    }
}
