#[path = "support/numeric_cast_recursive_oracle.rs"]
mod recursive_oracle;

use mettail_runtime::{
    numeric_float_bin, numeric_int_bin_i32, numeric_int_bin_i64, NumericInput, ProcToNumericInput,
};

#[derive(Debug)]
enum Proc {
    Int(i64),
    Float(f64),
    Text(String),
    IntBin(Option<Box<Proc>>, i64),
    FloatBin(Option<Box<Proc>>, i64),
    NonNumeric,
}

impl Drop for Proc {
    fn drop(&mut self) {
        let take_child = |node: &mut Proc| match node {
            Proc::IntBin(inner, _) | Proc::FloatBin(inner, _) => inner.take(),
            _ => None,
        };
        let mut next = take_child(self);
        while let Some(mut node) = next {
            next = take_child(&mut node);
        }
    }
}

impl ProcToNumericInput for Proc {
    fn to_numeric_input(&self) -> Option<NumericInput<'_>> {
        match self {
            Proc::Int(value) => Some(NumericInput::I64(*value)),
            Proc::Float(value) => Some(NumericInput::F64(*value)),
            _ => None,
        }
    }

    fn as_numeric_str(&self) -> Option<&str> {
        match self {
            Proc::Text(value) => Some(value),
            _ => None,
        }
    }

    fn as_int_bin(&self) -> Option<(&Self, i64)> {
        match self {
            Proc::IntBin(Some(inner), width) => Some((inner, *width)),
            _ => None,
        }
    }

    fn as_float_bin(&self) -> Option<(&Self, i64)> {
        match self {
            Proc::FloatBin(Some(inner), width) => Some((inner, *width)),
            _ => None,
        }
    }
}

fn int_bin(inner: Proc, width: i64) -> Proc {
    Proc::IntBin(Some(Box::new(inner)), width)
}

fn float_bin(inner: Proc, width: i64) -> Proc {
    Proc::FloatBin(Some(Box::new(inner)), width)
}

#[test]
fn iterative_casts_match_recursive_inner_then_outer_semantics() {
    let integer_corpus = [
        Proc::Int(257),
        Proc::Text("257".to_owned()),
        int_bin(Proc::Int(257), 16),
        int_bin(int_bin(Proc::Int(-129), 16), 8),
        int_bin(Proc::Int(1), 0),
        Proc::NonNumeric,
    ];
    for value in &integer_corpus {
        for width in [1, 8, 16, 32, 64] {
            assert_eq!(numeric_int_bin_i32(value, width), recursive_oracle::int_i32(value, width));
            assert_eq!(numeric_int_bin_i64(value, width), recursive_oracle::int_i64(value, width));
        }
    }

    let float_corpus = [
        Proc::Float(1.0 / 10.0),
        Proc::Text("0.1".to_owned()),
        float_bin(Proc::Float(1.0 / 10.0), 32),
        float_bin(float_bin(Proc::Float(16_777_217.0), 32), 64),
        float_bin(Proc::Float(1.0), 7),
        Proc::NonNumeric,
    ];
    for value in &float_corpus {
        for width in [32, 64] {
            assert_eq!(numeric_float_bin(value, width), recursive_oracle::float(value, width));
        }
    }
}

#[test]
fn iterative_casts_are_stack_safe_at_twenty_thousand_wrappers() {
    std::thread::Builder::new()
        .name("numeric-cast-pda-stack-gate".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut integer = Proc::Int(7);
            let mut float = Proc::Float(0.25);
            for _ in 0..20_000 {
                integer = int_bin(integer, 64);
                float = float_bin(float, 64);
            }
            assert_eq!(numeric_int_bin_i64(&integer, 64), Some(7));
            assert_eq!(numeric_float_bin(&float, 64).map(|value| value.get()), Some(0.25));
        })
        .expect("spawn numeric-cast PDA stack-gate thread")
        .join()
        .expect("numeric-cast PDA overflowed or panicked");
}
