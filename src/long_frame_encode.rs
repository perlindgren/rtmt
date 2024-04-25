// long_frame_encode

#[derive(Debug)]
struct State {
    first: Option<usize>,
    len: i8,
    has_zero: bool,
}

#[derive(Debug, Default)]
pub struct NcEncode {
    states: Vec<State>,
}

impl NcEncode {
    /// create a new encoder
    pub fn new() -> Self {
        NcEncode { states: vec![] }
    }

    /// open a new frame
    pub fn frame_begin(&mut self, len: usize) {
        let first = len % 127;
        println!("len {} first {}", len, first);

        self.states.push(State {
            first: if first == 0 { None } else { Some(first) },
            len: 0,
            has_zero: false,
        });
    }

    /// close current frame
    pub fn frame_end(&mut self) -> Vec<i8> {
        let inner_state = self.states.pop().unwrap();
        vec![
            if inner_state.has_zero {
                // length to next zero
                inner_state.len
            } else {
                println!("-- len {}", inner_state.len);
                // length to prev package
                (-inner_state.len) - 1
            },
            0,
        ]
    }

    /// encode a frame
    pub fn encode_frame(&mut self, data: &[i8]) -> Vec<i8> {
        let mut v: Vec<i8> = vec![];
        self.frame_begin(data.len());

        for d in data {
            v.append(&mut self.encode(*d))
        }

        v.append(&mut self.frame_end());
        v
    }

    /// encode a (signed) byte
    pub fn encode(&mut self, data: i8) -> Vec<i8> {
        let state = self.states.last_mut().unwrap();
        if data == 0 {
            let len = if state.has_zero {
                state.len
            } else {
                -(state.len + 1)
            };
            state.len = 1;

            state.has_zero = true;
            vec![len]
        } else if let Some(v) = {
            if state.len == 127 {
                panic!("--------------------------------");
                Some(-128)
            } else if let Some(first) = state.first {
                if state.len as usize == first {
                    println!("---- here ----");
                    state.first = None;
                    Some(-(first as i8 + 1))
                } else {
                    None
                }
            } else {
                None
            }
        } {
            // either first frame or chain of full frames
            state.len = 1;
            vec![v, data]
        } else {
            state.len += 1;
            vec![data]
        }
    }
}
