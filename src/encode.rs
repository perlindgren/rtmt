//

#[derive(Debug)]
struct State {
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
    pub fn frame_begin(&mut self) {
        self.states.push(State {
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
                // length to prev package
                -(inner_state.len + 1)
            },
            0,
        ]
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
        } else if state.len == 127 {
            state.len = 1;
            vec![-128, data]
        } else {
            state.len += 1;
            vec![data]
        }
    }
}
