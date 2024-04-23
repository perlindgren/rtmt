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
    pub fn clear(&mut self) {
        self.out_buf = VecDeque::new();
    }

    // scan frame recursively
    pub fn scan_frame(&mut self, mut p: i32, skip: bool) -> i32 {
        println!("scan_frame p {}, skip {}", p, skip);
        let offset = self.in_buf[p as usize];
        let mut is_end = offset > 0;
        let mut next: i32 = p - offset.abs() as i32;
        p -= 1;

        loop {
            println!("loop: is_end {}, p {}, next {}", is_end, p, next);
            if is_end && p == next {
                println!("frame done p {}, frame {:?}", p, self.out_buf);
                return p;
            }

            let data = self.in_buf[p as usize];
            if data == 0 {
                println!("preemption package at p {}", p);
                let new_p = self.scan_frame(p - 1, true);
                next -= p - new_p;
                p = new_p;
                println!("continue");
                continue;
            } else {
                println!("p {}, next {}, data {}", p, next, data);

                if p == next && !is_end {
                    if !skip {
                        println!("replace sentinel");
                        self.out_buf.push_front(0);
                    }
                    is_end = data > 0;
                    next -= data.abs() as i32;
                } else if !skip {
                    println!("----------- push data {}", data);
                    self.out_buf.push_front(data);
                }
                p -= 1;
            }
        }
    }

    pub fn decode(&mut self, data: i8) -> bool {
        let nc = self;
        println!("data {}", data);
        nc.in_buf.push(data);

        if data == 0 {
            println!("in_buf {:?}", nc.in_buf);
            let r = nc.scan_frame((nc.in_buf.len() - 2) as i32, false);
            println!("r {}", r);
            true
        } else {
            false
        }
    }
}

