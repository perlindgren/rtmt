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

    // encode a (signed) byte
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[allow(non_snake_case)]
    fn encode_ABC() {
        let mut nc = NcEncode::new();
        let mut s = vec![];
        nc.frame_begin();

        s.push(nc.encode(65));
        s.push(nc.encode(66));
        s.push(nc.encode(67));

        s.append(&mut nc.frame_end());
        println!("s {:?}", s);
        assert_eq!(s, [65, 66, 67, 4, 0].as_slice())
    }

    #[test]
    #[allow(non_snake_case)]
    fn encode_0() {
        let mut nc = NcEncode::new();
        let mut s = vec![];
        nc.frame_begin();
        s.push(nc.encode(0));
        s.append(&mut nc.frame_end());
        println!("s {:?}", s);
        assert_eq!(s, [1, -1, 0].as_slice())
    }

    #[test]
    #[allow(non_snake_case)]
    fn encode_00() {
        let mut nc = NcEncode::new();
        let mut s = vec![];
        nc.frame_begin();
        s.push(nc.encode(0));
        s.push(nc.encode(0));
        s.append(&mut nc.frame_end());
        println!("s {:?}", s);
        assert_eq!(s, [1, -1, -1, 0].as_slice())
    }

    #[test]
    #[allow(non_snake_case)]
    fn encode_A0() {
        let mut nc = NcEncode::new();
        let mut s = vec![];
        nc.frame_begin();
        s.push(nc.encode(65));
        s.push(nc.encode(0));
        s.append(&mut nc.frame_end());
        println!("s {:?}", s);
        assert_eq!(s, [65, 2, -1, 0].as_slice())
    }

    #[test]
    #[allow(non_snake_case)]
    fn encode_A00B0() {
        let mut nc = NcEncode::new();
        let mut s = vec![];
        nc.frame_begin();
        s.push(nc.encode(65));
        s.push(nc.encode(0));
        s.push(nc.encode(0));
        s.push(nc.encode(66));
        s.push(nc.encode(0));
        s.append(&mut nc.frame_end());
        println!("s {:?}", s);
        assert_eq!(s, [65, 2, -1, 66, -2, -1, 0].as_slice())
    }

    #[test]
    #[allow(non_snake_case)]
    fn encode_A_a_B_preempt() {
        let mut nc = NcEncode::new();
        let mut s = vec![];
        nc.frame_begin();
        s.push(nc.encode(65));

        nc.frame_begin();
        s.push(nc.encode(97));
        s.append(&mut nc.frame_end());

        s.push(nc.encode(66));
        s.append(&mut nc.frame_end());
        println!("s {:?}", s);
        assert_eq!(s, [65, 97, 2, 0, 66, 3, 0].as_slice())
    }

    #[test]
    #[allow(non_snake_case)]
    fn encode_A_B_preempt() {
        let mut nc = NcEncode::new();
        let mut s = vec![];
        nc.frame_begin();
        s.push(nc.encode(65));

        nc.frame_begin();
        s.append(&mut nc.frame_end());

        s.push(nc.encode(66));
        s.append(&mut nc.frame_end());
        println!("s {:?}", s);
        assert_eq!(s, [65, 1, 0, 66, 3, 0].as_slice())
    }

    #[test]
    #[allow(non_snake_case)]
    fn encode_A_0_0_preempt() {
        let mut nc = NcEncode::new();
        let mut s = vec![];
        nc.frame_begin();
        s.push(nc.encode(65));

        nc.frame_begin();
        s.push(nc.encode(0));
        s.append(&mut nc.frame_end());

        s.push(nc.encode(0));
        s.append(&mut nc.frame_end());
        println!("s {:?}", s);
        assert_eq!(s, [65, 1, -1, 0, 2, -1, 0].as_slice())
    }

    #[test]
    #[allow(non_snake_case)]
    fn encode_A00_0_0_preempt() {
        let mut nc = NcEncode::new();
        let mut s = vec![];
        nc.frame_begin();
        s.push(nc.encode(65));

        nc.frame_begin();
        s.push(nc.encode(0));
        s.append(&mut nc.frame_end());

        s.push(nc.encode(0));

        nc.frame_begin();
        s.push(nc.encode(0));
        s.append(&mut nc.frame_end());

        s.push(nc.encode(0));

        s.append(&mut nc.frame_end());
        println!("s {:?}", s);
        assert_eq!(s, [65, 1, -1, 0, 2, 1, -1, 0, -1, -1, 0].as_slice())
    }

    #[test]
    #[allow(non_snake_case)]
    fn encode_A0_0_a_preempt() {
        let mut nc = NcEncode::new();
        let mut s = vec![];
        nc.frame_begin();
        s.push(nc.encode(65));

        nc.frame_begin();
        s.push(nc.encode(0));

        nc.frame_begin();
        s.push(nc.encode(97));
        s.append(&mut nc.frame_end());

        s.append(&mut nc.frame_end());

        s.append(&mut nc.frame_end());
        println!("s {:?}", s);
        assert_eq!(s, [65, 1, 97, 2, 0, -1, 0, 2, -1, 0].as_slice())
    }

    #[test]
    #[allow(non_snake_case)]
    fn encode_AD_B_C_preempt() {
        let mut nc = NcEncode::new();
        let mut s = vec![];
        nc.frame_begin();
        s.push(nc.encode(65));

        nc.frame_begin();
        s.push(nc.encode(66));

        nc.frame_begin();
        s.push(nc.encode(67));
        s.append(&mut nc.frame_end());

        s.append(&mut nc.frame_end());

        s.push(nc.encode(68));

        s.append(&mut nc.frame_end());
        println!("s {:?}", s);
        assert_eq!(s, [65, 66, 67, 2, 0, 2, 0, 68, 3, 0].as_slice())
    }
}
