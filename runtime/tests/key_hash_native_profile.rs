//! Observe the actual compiler-generated Hash call shapes before extending
//! native admission. This tracer is not an execution or admission provider.

use mettail_runtime::{
    Binder, BoundVar, FltHoleId, FltSourceRange, FltTemplatePiece, FreeVar, OrdVar, Var,
};
use std::hash::{Hash, Hasher};

#[derive(Debug, PartialEq, Eq)]
enum Call {
    Fixed(&'static str),
    Bytes(usize),
}

#[derive(Default)]
struct NativeCalls(Vec<Call>);

macro_rules! fixed {
    ($method:ident, $ty:ty) => {
        fn $method(&mut self, _: $ty) {
            self.0.push(Call::Fixed(stringify!($method)));
        }
    };
}

impl Hasher for NativeCalls {
    fn finish(&self) -> u64 {
        panic!("a callback-shape probe does not compute a digest")
    }
    fn write(&mut self, bytes: &[u8]) {
        self.0.push(Call::Bytes(bytes.len()));
    }
    fixed!(write_u8, u8);
    fixed!(write_u16, u16);
    fixed!(write_u32, u32);
    fixed!(write_u64, u64);
    fixed!(write_u128, u128);
    fixed!(write_usize, usize);
    fixed!(write_i8, i8);
    fixed!(write_i16, i16);
    fixed!(write_i32, i32);
    fixed!(write_i64, i64);
    fixed!(write_i128, i128);
    fixed!(write_isize, isize);
}

fn calls(value: &impl Hash) -> Vec<Call> {
    let mut state = NativeCalls::default();
    value.hash(&mut state);
    state.0
}

fn assert_supported_enum_tag(call: &Call) {
    // Either signed-word forwarding or direct fixed-word hashing fits the
    // proposed three-group tag allowance on the audited 64-bit Fx profile.
    assert!(matches!(call, Call::Fixed("write_isize" | "write_usize" | "write_u64")));
}

#[test]
fn moniker_identity_hashes_do_not_visit_pretty_names() {
    let mut free: FreeVar<String> = FreeVar::fresh_named("x");
    let short = calls(&OrdVar(Var::Free(free.clone())));
    free.pretty_name = Some("x".repeat(1_000_000));
    let long = calls(&OrdVar(Var::Free(free.clone())));
    assert_eq!(short, long);
    assert_eq!(short.len(), 2);
    assert_supported_enum_tag(&short[0]);
    assert_eq!(short[1], Call::Fixed("write_u32"));
    assert_eq!(calls(&Binder(free.clone())), [Call::Fixed("write_u32")]);

    let mut bound = BoundVar {
        scope: moniker::ScopeOffset(2),
        binder: moniker::BinderIndex(3),
        pretty_name: None,
    };
    let unnamed = calls(&OrdVar(Var::Bound(bound.clone())));
    bound.pretty_name = free.pretty_name.clone();
    assert_eq!(unnamed, calls(&OrdVar(Var::Bound(bound))));
    assert_eq!(unnamed.len(), 3);
    assert_supported_enum_tag(&unnamed[0]);
    assert_eq!(unnamed[1..], [Call::Fixed("write_u32"), Call::Fixed("write_u32")]);
    println!("native variable calls: free={short:?}, bound={unnamed:?}");
}

#[test]
fn binder_vector_uses_length_prefix_and_each_identity_not_a_byte_slice() {
    let empty: Vec<Binder<String>> = Vec::new();
    assert_eq!(calls(&empty), [Call::Fixed("write_usize")]);
    let binder: Binder<String> = Binder(FreeVar::fresh_named("x".to_owned()));
    for width in [1, 2, 1000] {
        let values = vec![binder.clone(); width];
        let observed = calls(&values);
        assert_eq!(observed.len(), width + 1);
        assert_eq!(observed[0], Call::Fixed("write_usize"));
        assert!(observed[1..]
            .iter()
            .all(|call| *call == Call::Fixed("write_u32")));
    }
}

#[test]
fn option_and_flt_piece_hash_tags_fit_the_supported_header() {
    let none: Option<String> = None;
    let none_calls = calls(&none);
    assert_eq!(none_calls.len(), 1);
    assert_supported_enum_tag(&none_calls[0]);
    let some_calls = calls(&Some("λ".to_owned()));
    assert_eq!(some_calls.len(), 3);
    assert_supported_enum_tag(&some_calls[0]);
    assert_eq!(some_calls[1..], [Call::Bytes(2), Call::Fixed("write_u8")]);

    let range = FltSourceRange::new(5, 7);
    let text = calls(&FltTemplatePiece::Text { text: "λ".to_owned(), range });
    let hole = calls(&FltTemplatePiece::Hole { id: FltHoleId(2), range });
    assert_supported_enum_tag(&text[0]);
    assert_eq!(
        text[1..],
        [
            Call::Bytes(2),
            Call::Fixed("write_u8"),
            Call::Fixed("write_usize"),
            Call::Fixed("write_usize")
        ]
    );
    assert_supported_enum_tag(&hole[0]);
    assert_eq!(
        hole[1..],
        [Call::Fixed("write_u32"), Call::Fixed("write_usize"), Call::Fixed("write_usize")]
    );
    println!("native enum calls: option-none={none_calls:?}, option-some={some_calls:?}, text={text:?}, hole={hole:?}");
}
