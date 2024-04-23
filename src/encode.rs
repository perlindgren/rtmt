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
        println!("frame_begin");
        self.states.push(State {
            len: 0,
            has_zero: false,
        });
    }

    /// close current frame
    pub fn frame_end(&mut self) -> Vec<i8> {
        println!("frame_end");
        let inner_state = self.states.pop().unwrap();
        println!("inner_state {:?}", inner_state);

        if let Some(outer_state) = self.states.last_mut() {
            println!("outer_state {:?}", outer_state);
            // outer_state.len += inner_state.len + 2;
            println!("outer_state updated {:?}", outer_state);
        }

        vec![
            if inner_state.has_zero {
                // length to zero
                -inner_state.len
            } else {
                // length to start package
                inner_state.len + 1
            },
            0,
        ]
    }

    /// encode a (signed) byte
    pub fn encode(&mut self, data: i8) -> i8 {
        let state = self.states.last_mut().unwrap();
        println!("encode data {}, state {:?}", data, state);
        if data == 0 {
            let len = if state.has_zero {
                -state.len
            } else {
                state.len + 1
            };
            state.len = 1;

            state.has_zero = true;
            len
        } else {
            state.len += 1;
            data
        }
    }
}
