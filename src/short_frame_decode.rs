//

use std::collections::VecDeque;

#[derive(Debug, Default)]
pub struct NcDecode {
    in_buf: Vec<i8>,
    pub out_buf: VecDeque<i8>,
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
    pub fn clear_out(&mut self) {
        self.out_buf = VecDeque::new();
    }

    // clear input
    pub fn clear_in(&mut self) {
        self.in_buf = Vec::new();
    }

    // scan frame recursively
    pub fn scan_frame(&mut self, mut p: i32, skip: bool) -> i32 {
        let offset = self.in_buf[p as usize];
        let mut is_next_end = offset.is_negative();
        let mut next: i32 = p - (offset as i32).abs();
        p -= 1;

        loop {
            if is_next_end && p == next {
                return p;
            }

            let data = self.in_buf[p as usize];
            if data == 0 {
                let new_p = self.scan_frame(p - 1, true);
                next -= p - new_p;
                p = new_p;
                continue;
            } else {
                if p == next && !is_next_end {
                    if !skip {
                        self.out_buf.push_front(0);
                    }
                    is_next_end = data.is_negative();
                    next -= (data as i32).abs();
                } else if !skip {
                    self.out_buf.push_front(data);
                }
                p -= 1;
            }
        }
    }

    pub fn decode(&mut self, data: i8) -> Option<i32> {
        let de = self;
        de.in_buf.push(data);

        if data == 0 {
            Some(de.scan_frame((de.in_buf.len() - 2) as i32, false))
        } else {
            None
        }
    }
}
