/// Heterogeneous term wrapper for the tape-based builder.
#[allow(dead_code)]
#[derive(Clone)]
pub enum AnyTerm {
    WrapProc(Proc),
    WrapName(Name),
}
impl AnyTerm {
    /// Unwrap the inner `Proc` value, panicking if the variant is wrong.
    #[allow(dead_code)]
    pub fn unwrap_proc(self) -> Proc {
        match self {
            AnyTerm::WrapProc(v) => v,
            _ => panic!("AnyTerm::unwrap_proc: wrong variant"),
        }
    }
    /// Unwrap the inner `Name` value, panicking if the variant is wrong.
    #[allow(dead_code)]
    pub fn unwrap_name(self) -> Name {
        match self {
            AnyTerm::WrapName(v) => v,
            _ => panic!("AnyTerm::unwrap_name: wrong variant"),
        }
    }
}
/// Work item for the tape-based iterative term builder.
#[allow(dead_code)]
pub enum BuildTask {
    /// Build a Proc term at the given depth, storing result in the given slot.
    BuildProc { depth: u32, slot: usize },
    /// Build a Name term at the given depth, storing result in the given slot.
    BuildName { depth: u32, slot: usize },
}
/// Helper to consume bytes from a proptest-generated instruction tape.
#[allow(dead_code)]
pub struct TapeReader<'a> {
    tape: &'a [u8],
    pos: usize,
}
#[allow(dead_code)]
impl<'a> TapeReader<'a> {
    /// Create a new tape reader over the given byte slice.
    pub fn new(tape: &'a [u8]) -> Self {
        TapeReader { tape, pos: 0 }
    }
    /// Read the next byte, wrapping around if the tape is exhausted.
    pub fn next_byte(&mut self) -> u8 {
        if self.tape.is_empty() {
            return 0;
        }
        let b = self.tape[self.pos % self.tape.len()];
        self.pos += 1;
        b
    }
    /// Read a u32 from 4 bytes (little-endian), wrapping tape as needed.
    pub fn next_u32(&mut self) -> u32 {
        let b0 = self.next_byte() as u32;
        let b1 = self.next_byte() as u32;
        let b2 = self.next_byte() as u32;
        let b3 = self.next_byte() as u32;
        b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
    }
    /// Read an i32 from tape bytes.
    pub fn next_i32(&mut self) -> i32 {
        self.next_u32() as i32
    }
    /// Read an i64 from tape bytes.
    pub fn next_i64(&mut self) -> i64 {
        let lo = self.next_u32() as i64;
        let hi = self.next_u32() as i64;
        lo | (hi << 32)
    }
    /// Read an f64 from tape bytes.
    pub fn next_f64(&mut self) -> f64 {
        let bits = self.next_i64() as u64;
        let val = f64::from_bits(bits);
        if val.is_nan() || val.is_infinite() { 0.0 } else { val }
    }
    /// Read an f32 from tape bytes.
    pub fn next_f32(&mut self) -> f32 {
        let bits = self.next_u32();
        let val = f32::from_bits(bits);
        if val.is_nan() || val.is_infinite() { 0.0f32 } else { val }
    }
    /// Read a bool from tape.
    pub fn next_bool(&mut self) -> bool {
        self.next_byte() & 1 == 1
    }
    /// Read a short string from tape.
    pub fn next_string(&mut self) -> String {
        let len = (self.next_byte() % 8) as usize;
        (0..len)
            .map(|_| {
                let b = self.next_byte();
                (b'a' + (b % 26)) as char
            })
            .collect()
    }
}
/// Build a `Proc` term from an instruction tape.
///
/// Consumes bytes from the tape to choose constructors.
/// At depth 0, only leaf constructors (nullary, literal, var) are chosen.
/// At depth > 0, recursive constructors are also available.
#[allow(dead_code, unused_variables, clippy::let_and_return)]
pub fn build_proc_from_tape(reader: &mut TapeReader<'_>, depth: u32) -> Proc {
    if depth == 0 {
        let choice = (reader.next_byte() as usize) % 2;
        let result = match choice {
            0 => AnyTerm::WrapProc(Proc::PZero),
            _ => {
                let var_names = ["a", "b", "c", "x", "y", "z"];
                let idx = (reader.next_byte() as usize) % var_names.len();
                AnyTerm::WrapProc(
                    Proc::PVar(
                        mettail_runtime::OrdVar(
                            mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var(var_names[idx]),
                            ),
                        ),
                    ),
                )
            }
        };
        return result.unwrap_proc();
    }
    let choice = (reader.next_byte() as usize) % 8;
    let child_depth = depth - 1;
    match choice {
        0 => AnyTerm::WrapProc(Proc::PZero).unwrap_proc(),
        1 => {
            {
                let var_names = ["a", "b", "c", "x", "y", "z"];
                let idx = (reader.next_byte() as usize) % var_names.len();
                AnyTerm::WrapProc(
                    Proc::PVar(
                        mettail_runtime::OrdVar(
                            mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var(var_names[idx]),
                            ),
                        ),
                    ),
                )
            }
                .unwrap_proc()
        }
        2 => {
            let f0 = Box::new(build_name_from_tape(reader, child_depth));
            let f1 = Box::new(build_proc_from_tape(reader, child_depth));
            Proc::PIn(f0, f1)
        }
        3 => {
            let f0 = Box::new(build_name_from_tape(reader, child_depth));
            let f1 = Box::new(build_proc_from_tape(reader, child_depth));
            Proc::POut(f0, f1)
        }
        4 => {
            let f0 = Box::new(build_name_from_tape(reader, child_depth));
            let f1 = Box::new(build_proc_from_tape(reader, child_depth));
            Proc::POpen(f0, f1)
        }
        5 => {
            let f0 = Box::new(build_name_from_tape(reader, child_depth));
            let f1 = Box::new(build_proc_from_tape(reader, child_depth));
            Proc::PAmb(f0, f1)
        }
        6 => {
            let binder_name = format!("v{}", reader.next_byte() % 8);
            let binder = mettail_runtime::Binder(
                mettail_runtime::get_or_create_var(&binder_name),
            );
            let body = build_proc_from_tape(reader, child_depth);
            let scope = mettail_runtime::Scope::new(binder, Box::new(body));
            Proc::PNew(scope)
        }
        _ => {
            let num_elems = (reader.next_byte() % 4) as usize;
            let mut bag = mettail_runtime::HashBag::new();
            for _ in 0..num_elems {
                bag.insert(build_proc_from_tape(reader, child_depth));
            }
            Proc::PPar(bag)
        }
    }
}
/// Build a `Name` term from an instruction tape.
///
/// Consumes bytes from the tape to choose constructors.
/// At depth 0, only leaf constructors (nullary, literal, var) are chosen.
/// At depth > 0, recursive constructors are also available.
#[allow(dead_code, unused_variables, clippy::let_and_return)]
pub fn build_name_from_tape(reader: &mut TapeReader<'_>, depth: u32) -> Name {
    if depth == 0 {
        let result = {
            let var_names = ["a", "b", "c", "x", "y", "z"];
            let idx = (reader.next_byte() as usize) % var_names.len();
            AnyTerm::WrapName(
                Name::NVar(
                    mettail_runtime::OrdVar(
                        mettail_runtime::Var::Free(
                            mettail_runtime::get_or_create_var(var_names[idx]),
                        ),
                    ),
                ),
            )
        };
        return result.unwrap_name();
    }
    build_name_from_tape(reader, 0)
}
/// Generate an arbitrary `Proc` term with bounded depth.
///
/// Uses a flat `Vec<u8>` tape interpreted by `build_proc_from_tape`.
/// Proptest shrinking produces shorter tapes = simpler terms.
#[allow(dead_code)]
pub fn arb_proc(max_depth: u32) -> BoxedStrategy<Proc> {
    let max_tape = (10 * (max_depth as usize + 1)).max(20);
    proptest::collection::vec(proptest::prelude::any::<u8>(), 1..max_tape)
        .prop_map(move |tape| {
            let mut reader = TapeReader::new(&tape);
            build_proc_from_tape(&mut reader, max_depth)
        })
        .boxed()
}
/// Generate an arbitrary `Name` term with bounded depth.
///
/// Uses a flat `Vec<u8>` tape interpreted by `build_name_from_tape`.
/// Proptest shrinking produces shorter tapes = simpler terms.
#[allow(dead_code)]
pub fn arb_name(max_depth: u32) -> BoxedStrategy<Name> {
    let max_tape = (10 * (max_depth as usize + 1)).max(20);
    proptest::collection::vec(proptest::prelude::any::<u8>(), 1..max_tape)
        .prop_map(move |tape| {
            let mut reader = TapeReader::new(&tape);
            build_name_from_tape(&mut reader, max_depth)
        })
        .boxed()
}
