pub fn is_fresh<T>(binder: &mettail_runtime::Binder<String>, term: &T) -> bool
where
    T: mettail_runtime::BoundTerm<String>,
{
    use mettail_runtime::BoundTerm;
    let mut is_fresh = true;
    term.visit_vars(
        &mut |v| {
            if let mettail_runtime::Var::Free(fv) = v {
                if fv == &binder.0 {
                    is_fresh = false;
                }
            }
        },
    );
    is_fresh
}
