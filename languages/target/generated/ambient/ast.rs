#[derive(mettail_runtime::BoundTerm)]
pub enum Proc {
    PZero,
    PIn(Box<Name>, Box<Proc>),
    POut(Box<Name>, Box<Proc>),
    POpen(Box<Name>, Box<Proc>),
    PAmb(Box<Name>, Box<Proc>),
    PNew(mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<Proc>>),
    PPar(mettail_runtime::HashBag<Proc>),
    PVar(mettail_runtime::OrdVar),
    LamProc(mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<Proc>>),
    MLamProc(mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, Box<Proc>>),
    ApplyProc(Box<Proc>, Box<Proc>),
    MApplyProc(Box<Proc>, Vec<Proc>),
    LamName(mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<Proc>>),
    MLamName(mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, Box<Proc>>),
    ApplyName(Box<Proc>, Box<Name>),
    MApplyName(Box<Proc>, Vec<Name>),
}
#[derive(mettail_runtime::BoundTerm)]
pub enum Name {
    NVar(mettail_runtime::OrdVar),
    LamProc(mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<Name>>),
    MLamProc(mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, Box<Name>>),
    ApplyProc(Box<Name>, Box<Proc>),
    MApplyProc(Box<Name>, Vec<Proc>),
    LamName(mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<Name>>),
    MLamName(mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, Box<Name>>),
    ApplyName(Box<Name>, Box<Name>),
    MApplyName(Box<Name>, Vec<Name>),
}
/// Work item for the iterative Debug engine.
///
/// Each category variant wraps a raw pointer to a term to format.
/// The pointer is derived from a `&Cat` reference within the same
/// `fmt()` call, so the referent is guaranteed to be alive for the
/// duration. `WriteStr` and `WriteString` emit literal text (commas,
/// parens, field separators).
#[allow(dead_code)]
enum DebugTask {
    DebugProc(*const Proc),
    DebugName(*const Name),
    /// Write a static string literal.
    WriteStr(&'static str),
    /// Write an owned string.
    WriteString(String),
}
thread_local! {
    #[doc = r" Pool for reusing `DebugTask` work stacks across `Debug::fmt` calls."]
    static DEBUG_TASK_POOL : std::cell::Cell < Vec < DebugTask >> =
    std::cell::Cell::new(Vec::new());
}
/// Iterative Debug engine.
///
/// Pops tasks from the work-stack and writes to the formatter.
/// Category tasks decompose into child tasks (pushed in reverse
/// order for correct left-to-right output). WriteStr/WriteString
/// tasks emit literal text.
#[allow(dead_code)]
fn debug_iterative(
    stack: &mut Vec<DebugTask>,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    while let Some(task) = stack.pop() {
        match task {
            DebugTask::WriteStr(s) => {
                f.write_str(s)?;
            }
            DebugTask::WriteString(ref s) => {
                f.write_str(s)?;
            }
            DebugTask::DebugProc(ptr) => {
                let term = unsafe { &*ptr };
                match term {
                    Proc::PZero => {
                        f.write_str("PZero")?;
                    }
                    Proc::PIn(f0, f1) => {
                        f.write_str("PIn")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::DebugProc(&**f1 as *const _));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugName(&**f0 as *const _));
                    }
                    Proc::POut(f0, f1) => {
                        f.write_str("POut")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::DebugProc(&**f1 as *const _));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugName(&**f0 as *const _));
                    }
                    Proc::POpen(f0, f1) => {
                        f.write_str("POpen")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::DebugProc(&**f1 as *const _));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugName(&**f0 as *const _));
                    }
                    Proc::PAmb(f0, f1) => {
                        f.write_str("PAmb")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::DebugProc(&**f1 as *const _));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugName(&**f0 as *const _));
                    }
                    Proc::PNew(f0) => {
                        f.write_str("PNew")?;
                        f.write_str("(")?;
                        let inner = f0.inner();
                        f.write_str("Scope { pattern: ")?;
                        std::fmt::Debug::fmt(&inner.unsafe_pattern, f)?;
                        f.write_str(", body: ")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteStr(" }"));
                        stack
                            .push(DebugTask::DebugProc(&*inner.unsafe_body as *const _));
                    }
                    Proc::PPar(coll) => {
                        f.write_str("PPar")?;
                        f.write_str("(")?;
                        std::fmt::Debug::fmt(&coll, f)?;
                        f.write_str(")")?;
                    }
                    Proc::PVar(var) => {
                        f.write_str("PVar")?;
                        f.write_str("(")?;
                        std::fmt::Debug::fmt(&var, f)?;
                        f.write_str(")")?;
                    }
                    Proc::LamProc(f0) => {
                        f.write_str("LamProc")?;
                        f.write_str("(")?;
                        let inner = f0.inner();
                        f.write_str("Scope { pattern: ")?;
                        std::fmt::Debug::fmt(&inner.unsafe_pattern, f)?;
                        f.write_str(", body: ")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteStr(" }"));
                        stack
                            .push(DebugTask::DebugProc(&*inner.unsafe_body as *const _));
                    }
                    Proc::MLamProc(f0) => {
                        f.write_str("MLamProc")?;
                        f.write_str("(")?;
                        let inner = f0.inner();
                        f.write_str("Scope { pattern: ")?;
                        std::fmt::Debug::fmt(&inner.unsafe_pattern, f)?;
                        f.write_str(", body: ")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteStr(" }"));
                        stack
                            .push(DebugTask::DebugProc(&*inner.unsafe_body as *const _));
                    }
                    Proc::ApplyProc(f0, f1) => {
                        f.write_str("ApplyProc")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::DebugProc(&**f1 as *const _));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugProc(&**f0 as *const _));
                    }
                    Proc::MApplyProc(f0, f1) => {
                        f.write_str("MApplyProc")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteString(format!("{:?}", f1)));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugProc(&**f0 as *const _));
                    }
                    Proc::LamName(f0) => {
                        f.write_str("LamName")?;
                        f.write_str("(")?;
                        let inner = f0.inner();
                        f.write_str("Scope { pattern: ")?;
                        std::fmt::Debug::fmt(&inner.unsafe_pattern, f)?;
                        f.write_str(", body: ")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteStr(" }"));
                        stack
                            .push(DebugTask::DebugProc(&*inner.unsafe_body as *const _));
                    }
                    Proc::MLamName(f0) => {
                        f.write_str("MLamName")?;
                        f.write_str("(")?;
                        let inner = f0.inner();
                        f.write_str("Scope { pattern: ")?;
                        std::fmt::Debug::fmt(&inner.unsafe_pattern, f)?;
                        f.write_str(", body: ")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteStr(" }"));
                        stack
                            .push(DebugTask::DebugProc(&*inner.unsafe_body as *const _));
                    }
                    Proc::ApplyName(f0, f1) => {
                        f.write_str("ApplyName")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::DebugName(&**f1 as *const _));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugProc(&**f0 as *const _));
                    }
                    Proc::MApplyName(f0, f1) => {
                        f.write_str("MApplyName")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteString(format!("{:?}", f1)));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugProc(&**f0 as *const _));
                    }
                }
            }
            DebugTask::DebugName(ptr) => {
                let term = unsafe { &*ptr };
                match term {
                    Name::NVar(var) => {
                        f.write_str("NVar")?;
                        f.write_str("(")?;
                        std::fmt::Debug::fmt(&var, f)?;
                        f.write_str(")")?;
                    }
                    Name::LamProc(f0) => {
                        f.write_str("LamProc")?;
                        f.write_str("(")?;
                        let inner = f0.inner();
                        f.write_str("Scope { pattern: ")?;
                        std::fmt::Debug::fmt(&inner.unsafe_pattern, f)?;
                        f.write_str(", body: ")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteStr(" }"));
                        stack
                            .push(DebugTask::DebugName(&*inner.unsafe_body as *const _));
                    }
                    Name::MLamProc(f0) => {
                        f.write_str("MLamProc")?;
                        f.write_str("(")?;
                        let inner = f0.inner();
                        f.write_str("Scope { pattern: ")?;
                        std::fmt::Debug::fmt(&inner.unsafe_pattern, f)?;
                        f.write_str(", body: ")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteStr(" }"));
                        stack
                            .push(DebugTask::DebugName(&*inner.unsafe_body as *const _));
                    }
                    Name::ApplyProc(f0, f1) => {
                        f.write_str("ApplyProc")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::DebugProc(&**f1 as *const _));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugName(&**f0 as *const _));
                    }
                    Name::MApplyProc(f0, f1) => {
                        f.write_str("MApplyProc")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteString(format!("{:?}", f1)));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugName(&**f0 as *const _));
                    }
                    Name::LamName(f0) => {
                        f.write_str("LamName")?;
                        f.write_str("(")?;
                        let inner = f0.inner();
                        f.write_str("Scope { pattern: ")?;
                        std::fmt::Debug::fmt(&inner.unsafe_pattern, f)?;
                        f.write_str(", body: ")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteStr(" }"));
                        stack
                            .push(DebugTask::DebugName(&*inner.unsafe_body as *const _));
                    }
                    Name::MLamName(f0) => {
                        f.write_str("MLamName")?;
                        f.write_str("(")?;
                        let inner = f0.inner();
                        f.write_str("Scope { pattern: ")?;
                        std::fmt::Debug::fmt(&inner.unsafe_pattern, f)?;
                        f.write_str(", body: ")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteStr(" }"));
                        stack
                            .push(DebugTask::DebugName(&*inner.unsafe_body as *const _));
                    }
                    Name::ApplyName(f0, f1) => {
                        f.write_str("ApplyName")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::DebugName(&**f1 as *const _));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugName(&**f0 as *const _));
                    }
                    Name::MApplyName(f0, f1) => {
                        f.write_str("MApplyName")?;
                        f.write_str("(")?;
                        stack.push(DebugTask::WriteStr(")"));
                        stack.push(DebugTask::WriteString(format!("{:?}", f1)));
                        stack.push(DebugTask::WriteStr(", "));
                        stack.push(DebugTask::DebugName(&**f0 as *const _));
                    }
                }
            }
        }
    }
    Ok(())
}
impl std::fmt::Debug for Proc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let result = DEBUG_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                stack.clear();
                stack.push(DebugTask::DebugProc(self as *const Proc));
                let result = debug_iterative(&mut stack, f);
                cell.set(stack);
                result
            });
        match result {
            Ok(fmt_result) => fmt_result,
            Err(_) => {
                let mut stack = Vec::new();
                stack.push(DebugTask::DebugProc(self as *const Proc));
                debug_iterative(&mut stack, f)
            }
        }
    }
}
impl std::fmt::Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let result = DEBUG_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                stack.clear();
                stack.push(DebugTask::DebugName(self as *const Name));
                let result = debug_iterative(&mut stack, f);
                cell.set(stack);
                result
            });
        match result {
            Ok(fmt_result) => fmt_result,
            Err(_) => {
                let mut stack = Vec::new();
                stack.push(DebugTask::DebugName(self as *const Name));
                debug_iterative(&mut stack, f)
            }
        }
    }
}
impl Proc {
    /// Auto-flattening insert for #label
    ///
    /// If elem is itself a #label, recursively merges its contents instead of nesting.
    /// This ensures that collection constructors are always flat, never nested.
    pub fn insert_into_ppar(bag: &mut mettail_runtime::HashBag<Proc>, elem: Proc) {
        match elem {
            Proc::PPar(ref inner) => {
                for (e, count) in inner.iter() {
                    for _ in 0..count {
                        Self::insert_into_ppar(bag, e.clone());
                    }
                }
            }
            _ => {
                bag.insert(elem);
            }
        }
    }
}
impl Proc {
    /// Recursively normalize this term by:
    /// 1. Flattening nested collections (e.g., `PPar({PPar({a, b}), c})` becomes `PPar({a, b, c})`)
    /// 2. Performing immediate beta-reduction (e.g., `Apply(Lam(^x.body), arg)` becomes `body[arg/x]`)
    /// 3. Eagerly collapsing cancellation pairs (e.g., `PDrop(NQuote(P))` becomes `P`)
    ///
    /// This ensures terms are always in canonical form with beta-redexes reduced.
    pub fn normalize(&self) -> Self {
        match self {
            Proc::ApplyProc(lam_box, arg_box) => {
                let lam_normalized = lam_box.as_ref().normalize();
                match &lam_normalized {
                    Proc::LamProc(scope) => {
                        let (binder, body) = scope.clone().unbind();
                        let arg_normalized = arg_box.as_ref().normalize();
                        (*body).substitute_proc(&binder.0, &arg_normalized).normalize()
                    }
                    _ => {
                        Proc::ApplyProc(
                            Box::new(lam_normalized),
                            Box::new(arg_box.as_ref().normalize()),
                        )
                    }
                }
            }
            Proc::MApplyProc(lam_box, args) => {
                let lam_normalized = lam_box.as_ref().normalize();
                match &lam_normalized {
                    Proc::MLamProc(scope) => {
                        let (binders, body) = scope.clone().unbind();
                        let vars: Vec<_> = binders.iter().map(|b| &b.0).collect();
                        let args_normalized: Vec<_> = args
                            .iter()
                            .map(|a| a.normalize())
                            .collect();
                        (*body)
                            .multi_substitute_proc(&vars, &args_normalized)
                            .normalize()
                    }
                    _ => {
                        Proc::MApplyProc(
                            Box::new(lam_normalized),
                            args.iter().map(|a| a.normalize()).collect(),
                        )
                    }
                }
            }
            Proc::ApplyName(lam_box, arg_box) => {
                let lam_normalized = lam_box.as_ref().normalize();
                match &lam_normalized {
                    Proc::LamName(scope) => {
                        let (binder, body) = scope.clone().unbind();
                        let arg_normalized = arg_box.as_ref().normalize();
                        (*body).substitute_name(&binder.0, &arg_normalized).normalize()
                    }
                    _ => {
                        Proc::ApplyName(
                            Box::new(lam_normalized),
                            Box::new(arg_box.as_ref().normalize()),
                        )
                    }
                }
            }
            Proc::MApplyName(lam_box, args) => {
                let lam_normalized = lam_box.as_ref().normalize();
                match &lam_normalized {
                    Proc::MLamName(scope) => {
                        let (binders, body) = scope.clone().unbind();
                        let vars: Vec<_> = binders.iter().map(|b| &b.0).collect();
                        let args_normalized: Vec<_> = args
                            .iter()
                            .map(|a| a.normalize())
                            .collect();
                        (*body)
                            .multi_substitute_name(&vars, &args_normalized)
                            .normalize()
                    }
                    _ => {
                        Proc::MApplyName(
                            Box::new(lam_normalized),
                            args.iter().map(|a| a.normalize()).collect(),
                        )
                    }
                }
            }
            Proc::PZero => self.clone(),
            Proc::PIn(f0, f1) => {
                Proc::PIn(
                    Box::new(f0.as_ref().normalize()),
                    Box::new(f1.as_ref().normalize()),
                )
            }
            Proc::POut(f0, f1) => {
                Proc::POut(
                    Box::new(f0.as_ref().normalize()),
                    Box::new(f1.as_ref().normalize()),
                )
            }
            Proc::POpen(f0, f1) => {
                Proc::POpen(
                    Box::new(f0.as_ref().normalize()),
                    Box::new(f1.as_ref().normalize()),
                )
            }
            Proc::PAmb(f0, f1) => {
                Proc::PAmb(
                    Box::new(f0.as_ref().normalize()),
                    Box::new(f1.as_ref().normalize()),
                )
            }
            Proc::PNew(scope) => {
                Proc::PNew(
                    mettail_runtime::Scope::from_parts_unsafe(
                        scope.inner().unsafe_pattern.clone(),
                        Box::new(scope.inner().unsafe_body.as_ref().normalize()),
                    ),
                )
            }
            Proc::PPar(bag) => {
                let mut new_bag = mettail_runtime::HashBag::new();
                for (elem, count) in bag.iter() {
                    for _ in 0..count {
                        let normalized_elem = elem.normalize();
                        Self::insert_into_ppar(&mut new_bag, normalized_elem);
                    }
                }
                Proc::PPar(new_bag)
            }
            _ => self.clone(),
        }
    }
}
impl Name {
    /// Recursively normalize this term by:
    /// 1. Flattening nested collections (e.g., `PPar({PPar({a, b}), c})` becomes `PPar({a, b, c})`)
    /// 2. Performing immediate beta-reduction (e.g., `Apply(Lam(^x.body), arg)` becomes `body[arg/x]`)
    /// 3. Eagerly collapsing cancellation pairs (e.g., `PDrop(NQuote(P))` becomes `P`)
    ///
    /// This ensures terms are always in canonical form with beta-redexes reduced.
    pub fn normalize(&self) -> Self {
        match self {
            Name::ApplyProc(lam_box, arg_box) => {
                let lam_normalized = lam_box.as_ref().normalize();
                match &lam_normalized {
                    Name::LamProc(scope) => {
                        let (binder, body) = scope.clone().unbind();
                        let arg_normalized = arg_box.as_ref().normalize();
                        (*body).substitute_proc(&binder.0, &arg_normalized).normalize()
                    }
                    _ => {
                        Name::ApplyProc(
                            Box::new(lam_normalized),
                            Box::new(arg_box.as_ref().normalize()),
                        )
                    }
                }
            }
            Name::MApplyProc(lam_box, args) => {
                let lam_normalized = lam_box.as_ref().normalize();
                match &lam_normalized {
                    Name::MLamProc(scope) => {
                        let (binders, body) = scope.clone().unbind();
                        let vars: Vec<_> = binders.iter().map(|b| &b.0).collect();
                        let args_normalized: Vec<_> = args
                            .iter()
                            .map(|a| a.normalize())
                            .collect();
                        (*body)
                            .multi_substitute_proc(&vars, &args_normalized)
                            .normalize()
                    }
                    _ => {
                        Name::MApplyProc(
                            Box::new(lam_normalized),
                            args.iter().map(|a| a.normalize()).collect(),
                        )
                    }
                }
            }
            Name::ApplyName(lam_box, arg_box) => {
                let lam_normalized = lam_box.as_ref().normalize();
                match &lam_normalized {
                    Name::LamName(scope) => {
                        let (binder, body) = scope.clone().unbind();
                        let arg_normalized = arg_box.as_ref().normalize();
                        (*body).substitute_name(&binder.0, &arg_normalized).normalize()
                    }
                    _ => {
                        Name::ApplyName(
                            Box::new(lam_normalized),
                            Box::new(arg_box.as_ref().normalize()),
                        )
                    }
                }
            }
            Name::MApplyName(lam_box, args) => {
                let lam_normalized = lam_box.as_ref().normalize();
                match &lam_normalized {
                    Name::MLamName(scope) => {
                        let (binders, body) = scope.clone().unbind();
                        let vars: Vec<_> = binders.iter().map(|b| &b.0).collect();
                        let args_normalized: Vec<_> = args
                            .iter()
                            .map(|a| a.normalize())
                            .collect();
                        (*body)
                            .multi_substitute_name(&vars, &args_normalized)
                            .normalize()
                    }
                    _ => {
                        Name::MApplyName(
                            Box::new(lam_normalized),
                            args.iter().map(|a| a.normalize()).collect(),
                        )
                    }
                }
            }
            _ => self.clone(),
        }
    }
}
impl Proc {
    /// Single-variable substitution (same category)
    pub fn substitute(
        &self,
        var: &mettail_runtime::FreeVar<String>,
        replacement: &Self,
    ) -> Self {
        self.subst(&[var], &[replacement.clone()])
    }
    /// Multi-variable simultaneous substitution (capture-avoiding)
    pub fn subst(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Self],
    ) -> Self {
        if vars.is_empty() {
            return self.clone();
        }
        match self {
            Proc::PZero => self.clone(),
            Proc::PIn(f0, f1) => {
                Proc::PIn(
                    Box::new((**f0).subst_proc(vars, repls)),
                    Box::new((**f1).subst(vars, repls)),
                )
            }
            Proc::POut(f0, f1) => {
                Proc::POut(
                    Box::new((**f0).subst_proc(vars, repls)),
                    Box::new((**f1).subst(vars, repls)),
                )
            }
            Proc::POpen(f0, f1) => {
                Proc::POpen(
                    Box::new((**f0).subst_proc(vars, repls)),
                    Box::new((**f1).subst(vars, repls)),
                )
            }
            Proc::PAmb(f0, f1) => {
                Proc::PAmb(
                    Box::new((**f0).subst_proc(vars, repls)),
                    Box::new((**f1).subst(vars, repls)),
                )
            }
            Proc::PNew(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst(vars, repls);
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Proc::PNew(new_scope)
            }
            Proc::PPar(bag) => {
                let mut new_bag = mettail_runtime::HashBag::new();
                for (elem, count) in bag.iter() {
                    let s = elem.subst(vars, repls);
                    for _ in 0..count {
                        new_bag.insert(s.clone());
                    }
                }
                Proc::PPar(new_bag)
            }
            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                for (i, var) in vars.iter().enumerate() {
                    if v == *var {
                        return repls[i].clone();
                    }
                }
                self.clone()
            }
            Proc::PVar(_) => self.clone(),
            Proc::LamProc(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars
                    .iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| binder.0 != ***v)
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();
                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(new_body),
                    );
                    Proc::LamProc(new_scope)
                }
            }
            Proc::MLamProc(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars
                    .iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| !binders.iter().any(|b| &b.0 == **v))
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();
                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(
                        binders.clone(),
                        Box::new(new_body),
                    );
                    Proc::MLamProc(new_scope)
                }
            }
            Proc::ApplyProc(f0, f1) => {
                Proc::ApplyProc(
                    Box::new((**f0).subst(vars, repls)),
                    Box::new((**f1).subst(vars, repls)),
                )
            }
            Proc::MApplyProc(f0, f1) => {
                Proc::MApplyProc(
                    Box::new((**f0).subst(vars, repls)),
                    f1.iter().map(|elem| elem.subst(vars, repls)).collect(),
                )
            }
            Proc::LamName(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst(vars, repls);
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Proc::LamName(new_scope)
            }
            Proc::MLamName(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst(vars, repls);
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Proc::MLamName(new_scope)
            }
            Proc::ApplyName(f0, f1) => {
                Proc::ApplyName(
                    Box::new((**f0).subst(vars, repls)),
                    Box::new((**f1).subst_proc(vars, repls)),
                )
            }
            Proc::MApplyName(f0, f1) => {
                Proc::MApplyName(
                    Box::new((**f0).subst(vars, repls)),
                    f1.iter().map(|elem| elem.subst_proc(vars, repls)).collect(),
                )
            }
        }
    }
    /// Backward compatibility alias for multi_substitute
    #[inline]
    pub fn multi_substitute(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Self],
    ) -> Self {
        self.subst(vars, repls)
    }
    /// Alias for uniform cross-category calls
    #[inline]
    pub fn subst_proc(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Self],
    ) -> Self {
        self.subst(vars, repls)
    }
    /// Single-variable substitution alias (substitute_<category>)
    #[inline]
    pub fn substitute_proc(
        &self,
        var: &mettail_runtime::FreeVar<String>,
        replacement: &Self,
    ) -> Self {
        self.substitute(var, replacement)
    }
    /// Backward compatibility alias for multi_substitute_<category>
    #[inline]
    pub fn multi_substitute_proc(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Self],
    ) -> Self {
        self.subst(vars, repls)
    }
    /// Cross-category substitution: substitute #repl_cat values for #repl_cat variables
    pub fn subst_name(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Name],
    ) -> Self {
        if vars.is_empty() {
            return self.clone();
        }
        match self {
            Proc::PZero => self.clone(),
            Proc::PIn(f0, f1) => {
                Proc::PIn(
                    Box::new((**f0).subst(vars, repls)),
                    Box::new((**f1).subst_name(vars, repls)),
                )
            }
            Proc::POut(f0, f1) => {
                Proc::POut(
                    Box::new((**f0).subst(vars, repls)),
                    Box::new((**f1).subst_name(vars, repls)),
                )
            }
            Proc::POpen(f0, f1) => {
                Proc::POpen(
                    Box::new((**f0).subst(vars, repls)),
                    Box::new((**f1).subst_name(vars, repls)),
                )
            }
            Proc::PAmb(f0, f1) => {
                Proc::PAmb(
                    Box::new((**f0).subst(vars, repls)),
                    Box::new((**f1).subst_name(vars, repls)),
                )
            }
            Proc::PNew(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars
                    .iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| binder.0 != ***v)
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();
                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_name(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(new_body),
                    );
                    Proc::PNew(new_scope)
                }
            }
            Proc::PPar(bag) => {
                let mut new_bag = mettail_runtime::HashBag::new();
                for (elem, count) in bag.iter() {
                    let s = elem.subst_name(vars, repls);
                    for _ in 0..count {
                        new_bag.insert(s.clone());
                    }
                }
                Proc::PPar(new_bag)
            }
            Proc::PVar(_) => self.clone(),
            Proc::LamProc(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_name(vars, repls);
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Proc::LamProc(new_scope)
            }
            Proc::MLamProc(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_name(vars, repls);
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Proc::MLamProc(new_scope)
            }
            Proc::ApplyProc(f0, f1) => {
                Proc::ApplyProc(
                    Box::new((**f0).subst_name(vars, repls)),
                    Box::new((**f1).subst_name(vars, repls)),
                )
            }
            Proc::MApplyProc(f0, f1) => {
                Proc::MApplyProc(
                    Box::new((**f0).subst_name(vars, repls)),
                    f1.iter().map(|elem| elem.subst_name(vars, repls)).collect(),
                )
            }
            Proc::LamName(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars
                    .iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| binder.0 != ***v)
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();
                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_name(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(new_body),
                    );
                    Proc::LamName(new_scope)
                }
            }
            Proc::MLamName(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars
                    .iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| !binders.iter().any(|b| &b.0 == **v))
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();
                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_name(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(
                        binders.clone(),
                        Box::new(new_body),
                    );
                    Proc::MLamName(new_scope)
                }
            }
            Proc::ApplyName(f0, f1) => {
                Proc::ApplyName(
                    Box::new((**f0).subst_name(vars, repls)),
                    Box::new((**f1).subst(vars, repls)),
                )
            }
            Proc::MApplyName(f0, f1) => {
                Proc::MApplyName(
                    Box::new((**f0).subst_name(vars, repls)),
                    f1.iter().map(|elem| elem.subst(vars, repls)).collect(),
                )
            }
        }
    }
    /// Single-variable cross-category substitution (backward compatibility)
    #[inline]
    pub fn substitute_name(
        &self,
        var: &mettail_runtime::FreeVar<String>,
        replacement: &Name,
    ) -> Self {
        self.subst_name(&[var], &[replacement.clone()])
    }
    /// Multi-variable cross-category substitution (backward compatibility alias)
    #[inline]
    pub fn multi_substitute_name(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Name],
    ) -> Self {
        self.subst_name(vars, repls)
    }
}
impl Name {
    /// Single-variable substitution (same category)
    pub fn substitute(
        &self,
        var: &mettail_runtime::FreeVar<String>,
        replacement: &Self,
    ) -> Self {
        self.subst(&[var], &[replacement.clone()])
    }
    /// Multi-variable simultaneous substitution (capture-avoiding)
    pub fn subst(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Self],
    ) -> Self {
        if vars.is_empty() {
            return self.clone();
        }
        match self {
            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                for (i, var) in vars.iter().enumerate() {
                    if v == *var {
                        return repls[i].clone();
                    }
                }
                self.clone()
            }
            Name::NVar(_) => self.clone(),
            Name::LamProc(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst(vars, repls);
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Name::LamProc(new_scope)
            }
            Name::MLamProc(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst(vars, repls);
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Name::MLamProc(new_scope)
            }
            Name::ApplyProc(f0, f1) => {
                Name::ApplyProc(
                    Box::new((**f0).subst(vars, repls)),
                    Box::new((**f1).subst_name(vars, repls)),
                )
            }
            Name::MApplyProc(f0, f1) => {
                Name::MApplyProc(
                    Box::new((**f0).subst(vars, repls)),
                    f1.iter().map(|elem| elem.subst_name(vars, repls)).collect(),
                )
            }
            Name::LamName(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars
                    .iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| binder.0 != ***v)
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();
                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(new_body),
                    );
                    Name::LamName(new_scope)
                }
            }
            Name::MLamName(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars
                    .iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| !binders.iter().any(|b| &b.0 == **v))
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();
                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(
                        binders.clone(),
                        Box::new(new_body),
                    );
                    Name::MLamName(new_scope)
                }
            }
            Name::ApplyName(f0, f1) => {
                Name::ApplyName(
                    Box::new((**f0).subst(vars, repls)),
                    Box::new((**f1).subst(vars, repls)),
                )
            }
            Name::MApplyName(f0, f1) => {
                Name::MApplyName(
                    Box::new((**f0).subst(vars, repls)),
                    f1.iter().map(|elem| elem.subst(vars, repls)).collect(),
                )
            }
        }
    }
    /// Backward compatibility alias for multi_substitute
    #[inline]
    pub fn multi_substitute(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Self],
    ) -> Self {
        self.subst(vars, repls)
    }
    /// Alias for uniform cross-category calls
    #[inline]
    pub fn subst_name(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Self],
    ) -> Self {
        self.subst(vars, repls)
    }
    /// Single-variable substitution alias (substitute_<category>)
    #[inline]
    pub fn substitute_name(
        &self,
        var: &mettail_runtime::FreeVar<String>,
        replacement: &Self,
    ) -> Self {
        self.substitute(var, replacement)
    }
    /// Backward compatibility alias for multi_substitute_<category>
    #[inline]
    pub fn multi_substitute_name(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Self],
    ) -> Self {
        self.subst(vars, repls)
    }
    /// Cross-category substitution: substitute #repl_cat values for #repl_cat variables
    pub fn subst_proc(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Proc],
    ) -> Self {
        if vars.is_empty() {
            return self.clone();
        }
        match self {
            Name::NVar(_) => self.clone(),
            Name::LamProc(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars
                    .iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| binder.0 != ***v)
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();
                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_proc(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(new_body),
                    );
                    Name::LamProc(new_scope)
                }
            }
            Name::MLamProc(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars
                    .iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| !binders.iter().any(|b| &b.0 == **v))
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();
                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_proc(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(
                        binders.clone(),
                        Box::new(new_body),
                    );
                    Name::MLamProc(new_scope)
                }
            }
            Name::ApplyProc(f0, f1) => {
                Name::ApplyProc(
                    Box::new((**f0).subst_proc(vars, repls)),
                    Box::new((**f1).subst(vars, repls)),
                )
            }
            Name::MApplyProc(f0, f1) => {
                Name::MApplyProc(
                    Box::new((**f0).subst_proc(vars, repls)),
                    f1.iter().map(|elem| elem.subst(vars, repls)).collect(),
                )
            }
            Name::LamName(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_proc(vars, repls);
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Name::LamName(new_scope)
            }
            Name::MLamName(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_proc(vars, repls);
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Name::MLamName(new_scope)
            }
            Name::ApplyName(f0, f1) => {
                Name::ApplyName(
                    Box::new((**f0).subst_proc(vars, repls)),
                    Box::new((**f1).subst_proc(vars, repls)),
                )
            }
            Name::MApplyName(f0, f1) => {
                Name::MApplyName(
                    Box::new((**f0).subst_proc(vars, repls)),
                    f1.iter().map(|elem| elem.subst_proc(vars, repls)).collect(),
                )
            }
        }
    }
    /// Single-variable cross-category substitution (backward compatibility)
    #[inline]
    pub fn substitute_proc(
        &self,
        var: &mettail_runtime::FreeVar<String>,
        replacement: &Proc,
    ) -> Self {
        self.subst_proc(&[var], &[replacement.clone()])
    }
    /// Multi-variable cross-category substitution (backward compatibility alias)
    #[inline]
    pub fn multi_substitute_proc(
        &self,
        vars: &[&mettail_runtime::FreeVar<String>],
        repls: &[Proc],
    ) -> Self {
        self.subst_proc(vars, repls)
    }
}
/// Per-category environment for storing named term bindings (preserves insertion order)
#[derive(Debug, Clone, Default)]
pub struct ProcEnv(pub indexmap::IndexMap<std::string::String, Proc>);
impl ProcEnv {
    /// Create a new empty environment
    pub fn new() -> Self {
        Self(indexmap::IndexMap::new())
    }
    /// Get a term by name
    pub fn get(&self, name: &str) -> Option<&Proc> {
        self.0.get(name)
    }
    /// Set a term binding (maintains insertion order for new entries)
    pub fn set(&mut self, name: std::string::String, value: Proc) {
        self.0.insert(name, value);
    }
    /// Remove a term binding (maintains order of remaining entries)
    pub fn remove(&mut self, name: &str) -> Option<Proc> {
        self.0.shift_remove(name)
    }
    /// Iterate over all bindings in insertion order
    pub fn iter(&self) -> impl Iterator<Item = (&std::string::String, &Proc)> {
        self.0.iter()
    }
    /// Check if environment is empty
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Get the number of bindings
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Clear all bindings
    pub fn clear(&mut self) {
        self.0.clear()
    }
}
/// Per-category environment for storing named term bindings (preserves insertion order)
#[derive(Debug, Clone, Default)]
pub struct NameEnv(pub indexmap::IndexMap<std::string::String, Name>);
impl NameEnv {
    /// Create a new empty environment
    pub fn new() -> Self {
        Self(indexmap::IndexMap::new())
    }
    /// Get a term by name
    pub fn get(&self, name: &str) -> Option<&Name> {
        self.0.get(name)
    }
    /// Set a term binding (maintains insertion order for new entries)
    pub fn set(&mut self, name: std::string::String, value: Name) {
        self.0.insert(name, value);
    }
    /// Remove a term binding (maintains order of remaining entries)
    pub fn remove(&mut self, name: &str) -> Option<Name> {
        self.0.shift_remove(name)
    }
    /// Iterate over all bindings in insertion order
    pub fn iter(&self) -> impl Iterator<Item = (&std::string::String, &Name)> {
        self.0.iter()
    }
    /// Check if environment is empty
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Get the number of bindings
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Clear all bindings
    pub fn clear(&mut self) {
        self.0.clear()
    }
}
/// Combined environment for all categories in this theory
#[derive(Debug, Clone, Default)]
pub struct AmbientEnv {
    pub proc: ProcEnv,
    pub name: NameEnv,
    /// Optional comments for each binding (keyed by binding name)
    pub comments: std::collections::HashMap<std::string::String, std::string::String>,
}
impl AmbientEnv {
    /// Create a new empty environment
    pub fn new() -> Self {
        Self {
            proc: ProcEnv::new(),
            name: NameEnv::new(),
            comments: std::collections::HashMap::new(),
        }
    }
    /// Clear all bindings from all categories
    pub fn clear(&mut self) {
        self.proc.clear();
        self.name.clear();
        self.comments.clear();
    }
    /// Check if all environments are empty
    pub fn is_empty(&self) -> bool {
        self.proc.is_empty() && self.name.is_empty()
    }
    /// Set a comment for a binding
    pub fn set_comment(&mut self, name: &str, comment: std::string::String) {
        self.comments.insert(name.to_string(), comment);
    }
    /// Get the comment for a binding
    pub fn get_comment(&self, name: &str) -> Option<&std::string::String> {
        self.comments.get(name)
    }
    /// Remove a comment for a binding
    pub fn remove_comment(&mut self, name: &str) {
        self.comments.remove(name);
    }
}
impl Proc {
    /// Substitute all environment variables in this term by name
    ///
    /// Replaces all free variables whose names match keys in the environment
    /// with their corresponding values. Uses name-based matching (not FreeVar identity).
    /// Iterates until fixed point (no more substitutions possible).
    /// Finally normalizes FreeVar IDs and flattens any nested collections.
    pub fn substitute_env(&self, env: &AmbientEnv) -> Self {
        let mut result = self.clone();
        for _ in 0..100 {
            let prev_str = format!("{}", result);
            result = result.subst_by_name_proc(&env.proc.0);
            result = result.subst_by_name_name(&env.name.0);
            if format!("{}", result) == prev_str {
                break;
            }
        }
        let result = result.unify_freevars();
        result.normalize()
    }
    /// Substitute variables by name from a map (preserves insertion order)
    fn subst_by_name_proc(&self, env_map: &indexmap::IndexMap<String, Proc>) -> Self {
        if env_map.is_empty() {
            return self.clone();
        }
        match self {
            Proc::PZero => self.clone(),
            Proc::PIn(f0, f1) => {
                Proc::PIn(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    Box::new((**f1).subst_by_name_proc(env_map)),
                )
            }
            Proc::POut(f0, f1) => {
                Proc::POut(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    Box::new((**f1).subst_by_name_proc(env_map)),
                )
            }
            Proc::POpen(f0, f1) => {
                Proc::POpen(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    Box::new((**f1).subst_by_name_proc(env_map)),
                )
            }
            Proc::PAmb(f0, f1) => {
                Proc::PAmb(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    Box::new((**f1).subst_by_name_proc(env_map)),
                )
            }
            Proc::PNew(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_by_name_proc(env_map);
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Proc::PNew(new_scope)
            }
            Proc::PPar(bag) => {
                let mut new_bag = mettail_runtime::HashBag::new();
                for (elem, count) in bag.iter() {
                    let s = elem.subst_by_name_proc(env_map);
                    for _ in 0..count {
                        new_bag.insert(s.clone());
                    }
                }
                Proc::PPar(new_bag)
            }
            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                if let Some(name) = &v.pretty_name {
                    if let Some(replacement) = env_map.get(name) {
                        return replacement.clone();
                    }
                }
                self.clone()
            }
            Proc::PVar(_) => self.clone(),
            Proc::LamProc(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let filtered_env: indexmap::IndexMap<String, Proc> = if let Some(name) = &binder
                    .0
                    .pretty_name
                {
                    env_map
                        .iter()
                        .filter(|(k, _)| *k != name)
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect()
                } else {
                    env_map.clone()
                };
                if filtered_env.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_by_name_proc(&filtered_env);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(new_body),
                    );
                    Proc::LamProc(new_scope)
                }
            }
            Proc::MLamProc(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let bound_names: std::collections::HashSet<String> = binders
                    .iter()
                    .filter_map(|b| b.0.pretty_name.clone())
                    .collect();
                let filtered_env: indexmap::IndexMap<String, Proc> = env_map
                    .iter()
                    .filter(|(k, _)| !bound_names.contains(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();
                if filtered_env.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_by_name_proc(&filtered_env);
                    let new_scope = mettail_runtime::Scope::new(
                        binders.clone(),
                        Box::new(new_body),
                    );
                    Proc::MLamProc(new_scope)
                }
            }
            Proc::ApplyProc(f0, f1) => {
                Proc::ApplyProc(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    Box::new((**f1).subst_by_name_proc(env_map)),
                )
            }
            Proc::MApplyProc(f0, f1) => {
                Proc::MApplyProc(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    f1.iter().map(|elem| elem.subst_by_name_proc(env_map)).collect(),
                )
            }
            Proc::LamName(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_by_name_proc(env_map);
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Proc::LamName(new_scope)
            }
            Proc::MLamName(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_by_name_proc(env_map);
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Proc::MLamName(new_scope)
            }
            Proc::ApplyName(f0, f1) => {
                Proc::ApplyName(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    Box::new((**f1).subst_by_name_proc(env_map)),
                )
            }
            Proc::MApplyName(f0, f1) => {
                Proc::MApplyName(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    f1.iter().map(|elem| elem.subst_by_name_proc(env_map)).collect(),
                )
            }
        }
    }
    /// Substitute variables by name from a map (preserves insertion order)
    fn subst_by_name_name(&self, env_map: &indexmap::IndexMap<String, Name>) -> Self {
        if env_map.is_empty() {
            return self.clone();
        }
        match self {
            Proc::PZero => self.clone(),
            Proc::PIn(f0, f1) => {
                Proc::PIn(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    Box::new((**f1).subst_by_name_name(env_map)),
                )
            }
            Proc::POut(f0, f1) => {
                Proc::POut(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    Box::new((**f1).subst_by_name_name(env_map)),
                )
            }
            Proc::POpen(f0, f1) => {
                Proc::POpen(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    Box::new((**f1).subst_by_name_name(env_map)),
                )
            }
            Proc::PAmb(f0, f1) => {
                Proc::PAmb(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    Box::new((**f1).subst_by_name_name(env_map)),
                )
            }
            Proc::PNew(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let filtered_env: indexmap::IndexMap<String, Name> = if let Some(name) = &binder
                    .0
                    .pretty_name
                {
                    env_map
                        .iter()
                        .filter(|(k, _)| *k != name)
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect()
                } else {
                    env_map.clone()
                };
                if filtered_env.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_by_name_name(&filtered_env);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(new_body),
                    );
                    Proc::PNew(new_scope)
                }
            }
            Proc::PPar(bag) => {
                let mut new_bag = mettail_runtime::HashBag::new();
                for (elem, count) in bag.iter() {
                    let s = elem.subst_by_name_name(env_map);
                    for _ in 0..count {
                        new_bag.insert(s.clone());
                    }
                }
                Proc::PPar(new_bag)
            }
            Proc::PVar(_) => self.clone(),
            Proc::LamProc(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_by_name_name(env_map);
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Proc::LamProc(new_scope)
            }
            Proc::MLamProc(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_by_name_name(env_map);
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Proc::MLamProc(new_scope)
            }
            Proc::ApplyProc(f0, f1) => {
                Proc::ApplyProc(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    Box::new((**f1).subst_by_name_name(env_map)),
                )
            }
            Proc::MApplyProc(f0, f1) => {
                Proc::MApplyProc(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    f1.iter().map(|elem| elem.subst_by_name_name(env_map)).collect(),
                )
            }
            Proc::LamName(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let filtered_env: indexmap::IndexMap<String, Name> = if let Some(name) = &binder
                    .0
                    .pretty_name
                {
                    env_map
                        .iter()
                        .filter(|(k, _)| *k != name)
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect()
                } else {
                    env_map.clone()
                };
                if filtered_env.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_by_name_name(&filtered_env);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(new_body),
                    );
                    Proc::LamName(new_scope)
                }
            }
            Proc::MLamName(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let bound_names: std::collections::HashSet<String> = binders
                    .iter()
                    .filter_map(|b| b.0.pretty_name.clone())
                    .collect();
                let filtered_env: indexmap::IndexMap<String, Name> = env_map
                    .iter()
                    .filter(|(k, _)| !bound_names.contains(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();
                if filtered_env.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_by_name_name(&filtered_env);
                    let new_scope = mettail_runtime::Scope::new(
                        binders.clone(),
                        Box::new(new_body),
                    );
                    Proc::MLamName(new_scope)
                }
            }
            Proc::ApplyName(f0, f1) => {
                Proc::ApplyName(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    Box::new((**f1).subst_by_name_name(env_map)),
                )
            }
            Proc::MApplyName(f0, f1) => {
                Proc::MApplyName(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    f1.iter().map(|elem| elem.subst_by_name_name(env_map)).collect(),
                )
            }
        }
    }
    /// Unify FreeVar IDs by pretty_name using the global VAR_CACHE.
    /// This ensures all variables with the same name have the same FreeVar ID,
    /// which is necessary for Ascent equality checks to work correctly
    /// when terms come from different parsing contexts (e.g., environment vs user input).
    pub fn unify_freevars(&self) -> Self {
        self.unify_freevars_impl()
    }
}
impl Name {
    /// Substitute all environment variables in this term by name
    ///
    /// Replaces all free variables whose names match keys in the environment
    /// with their corresponding values. Uses name-based matching (not FreeVar identity).
    /// Iterates until fixed point (no more substitutions possible).
    /// Finally normalizes FreeVar IDs and flattens any nested collections.
    pub fn substitute_env(&self, env: &AmbientEnv) -> Self {
        let mut result = self.clone();
        for _ in 0..100 {
            let prev_str = format!("{}", result);
            result = result.subst_by_name_proc(&env.proc.0);
            result = result.subst_by_name_name(&env.name.0);
            if format!("{}", result) == prev_str {
                break;
            }
        }
        let result = result.unify_freevars();
        result.normalize()
    }
    /// Substitute variables by name from a map (preserves insertion order)
    fn subst_by_name_proc(&self, env_map: &indexmap::IndexMap<String, Proc>) -> Self {
        if env_map.is_empty() {
            return self.clone();
        }
        match self {
            Name::NVar(_) => self.clone(),
            Name::LamProc(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let filtered_env: indexmap::IndexMap<String, Proc> = if let Some(name) = &binder
                    .0
                    .pretty_name
                {
                    env_map
                        .iter()
                        .filter(|(k, _)| *k != name)
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect()
                } else {
                    env_map.clone()
                };
                if filtered_env.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_by_name_proc(&filtered_env);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(new_body),
                    );
                    Name::LamProc(new_scope)
                }
            }
            Name::MLamProc(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let bound_names: std::collections::HashSet<String> = binders
                    .iter()
                    .filter_map(|b| b.0.pretty_name.clone())
                    .collect();
                let filtered_env: indexmap::IndexMap<String, Proc> = env_map
                    .iter()
                    .filter(|(k, _)| !bound_names.contains(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();
                if filtered_env.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_by_name_proc(&filtered_env);
                    let new_scope = mettail_runtime::Scope::new(
                        binders.clone(),
                        Box::new(new_body),
                    );
                    Name::MLamProc(new_scope)
                }
            }
            Name::ApplyProc(f0, f1) => {
                Name::ApplyProc(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    Box::new((**f1).subst_by_name_proc(env_map)),
                )
            }
            Name::MApplyProc(f0, f1) => {
                Name::MApplyProc(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    f1.iter().map(|elem| elem.subst_by_name_proc(env_map)).collect(),
                )
            }
            Name::LamName(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_by_name_proc(env_map);
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Name::LamName(new_scope)
            }
            Name::MLamName(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_by_name_proc(env_map);
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Name::MLamName(new_scope)
            }
            Name::ApplyName(f0, f1) => {
                Name::ApplyName(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    Box::new((**f1).subst_by_name_proc(env_map)),
                )
            }
            Name::MApplyName(f0, f1) => {
                Name::MApplyName(
                    Box::new((**f0).subst_by_name_proc(env_map)),
                    f1.iter().map(|elem| elem.subst_by_name_proc(env_map)).collect(),
                )
            }
        }
    }
    /// Substitute variables by name from a map (preserves insertion order)
    fn subst_by_name_name(&self, env_map: &indexmap::IndexMap<String, Name>) -> Self {
        if env_map.is_empty() {
            return self.clone();
        }
        match self {
            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                if let Some(name) = &v.pretty_name {
                    if let Some(replacement) = env_map.get(name) {
                        return replacement.clone();
                    }
                }
                self.clone()
            }
            Name::NVar(_) => self.clone(),
            Name::LamProc(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_by_name_name(env_map);
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Name::LamProc(new_scope)
            }
            Name::MLamProc(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).subst_by_name_name(env_map);
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Name::MLamProc(new_scope)
            }
            Name::ApplyProc(f0, f1) => {
                Name::ApplyProc(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    Box::new((**f1).subst_by_name_name(env_map)),
                )
            }
            Name::MApplyProc(f0, f1) => {
                Name::MApplyProc(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    f1.iter().map(|elem| elem.subst_by_name_name(env_map)).collect(),
                )
            }
            Name::LamName(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let filtered_env: indexmap::IndexMap<String, Name> = if let Some(name) = &binder
                    .0
                    .pretty_name
                {
                    env_map
                        .iter()
                        .filter(|(k, _)| *k != name)
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect()
                } else {
                    env_map.clone()
                };
                if filtered_env.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_by_name_name(&filtered_env);
                    let new_scope = mettail_runtime::Scope::new(
                        binder.clone(),
                        Box::new(new_body),
                    );
                    Name::LamName(new_scope)
                }
            }
            Name::MLamName(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let bound_names: std::collections::HashSet<String> = binders
                    .iter()
                    .filter_map(|b| b.0.pretty_name.clone())
                    .collect();
                let filtered_env: indexmap::IndexMap<String, Name> = env_map
                    .iter()
                    .filter(|(k, _)| !bound_names.contains(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();
                if filtered_env.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).subst_by_name_name(&filtered_env);
                    let new_scope = mettail_runtime::Scope::new(
                        binders.clone(),
                        Box::new(new_body),
                    );
                    Name::MLamName(new_scope)
                }
            }
            Name::ApplyName(f0, f1) => {
                Name::ApplyName(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    Box::new((**f1).subst_by_name_name(env_map)),
                )
            }
            Name::MApplyName(f0, f1) => {
                Name::MApplyName(
                    Box::new((**f0).subst_by_name_name(env_map)),
                    f1.iter().map(|elem| elem.subst_by_name_name(env_map)).collect(),
                )
            }
        }
    }
    /// Unify FreeVar IDs by pretty_name using the global VAR_CACHE.
    /// This ensures all variables with the same name have the same FreeVar ID,
    /// which is necessary for Ascent equality checks to work correctly
    /// when terms come from different parsing contexts (e.g., environment vs user input).
    pub fn unify_freevars(&self) -> Self {
        self.unify_freevars_impl()
    }
}
impl Proc {
    fn unify_freevars_impl(&self) -> Self {
        match self {
            Proc::PZero => Proc::PZero,
            Proc::PIn(f0, f1) => {
                Proc::PIn(
                    Box::new((**f0).unify_freevars_impl()),
                    Box::new((**f1).unify_freevars_impl()),
                )
            }
            Proc::POut(f0, f1) => {
                Proc::POut(
                    Box::new((**f0).unify_freevars_impl()),
                    Box::new((**f1).unify_freevars_impl()),
                )
            }
            Proc::POpen(f0, f1) => {
                Proc::POpen(
                    Box::new((**f0).unify_freevars_impl()),
                    Box::new((**f1).unify_freevars_impl()),
                )
            }
            Proc::PAmb(f0, f1) => {
                Proc::PAmb(
                    Box::new((**f0).unify_freevars_impl()),
                    Box::new((**f1).unify_freevars_impl()),
                )
            }
            Proc::PNew(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).unify_freevars_impl();
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Proc::PNew(new_scope)
            }
            Proc::PPar(bag) => {
                let mut new_bag = mettail_runtime::HashBag::new();
                for (elem, count) in bag.iter() {
                    let u = elem.unify_freevars_impl();
                    for _ in 0..count {
                        new_bag.insert(u.clone());
                    }
                }
                Proc::PPar(new_bag)
            }
            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                let canonical = mettail_runtime::get_or_insert_var(v);
                Proc::PVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(canonical)),
                )
            }
            Proc::PVar(bound) => Proc::PVar(bound.clone()),
            Proc::LamProc(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).unify_freevars_impl();
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Proc::LamProc(new_scope)
            }
            Proc::MLamProc(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).unify_freevars_impl();
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Proc::MLamProc(new_scope)
            }
            Proc::ApplyProc(f0, f1) => {
                Proc::ApplyProc(
                    Box::new((**f0).unify_freevars_impl()),
                    Box::new((**f1).unify_freevars_impl()),
                )
            }
            Proc::MApplyProc(f0, f1) => {
                Proc::MApplyProc(
                    Box::new((**f0).unify_freevars_impl()),
                    f1.iter().map(|e| e.unify_freevars_impl()).collect(),
                )
            }
            Proc::LamName(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).unify_freevars_impl();
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Proc::LamName(new_scope)
            }
            Proc::MLamName(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).unify_freevars_impl();
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Proc::MLamName(new_scope)
            }
            Proc::ApplyName(f0, f1) => {
                Proc::ApplyName(
                    Box::new((**f0).unify_freevars_impl()),
                    Box::new((**f1).unify_freevars_impl()),
                )
            }
            Proc::MApplyName(f0, f1) => {
                Proc::MApplyName(
                    Box::new((**f0).unify_freevars_impl()),
                    f1.iter().map(|e| e.unify_freevars_impl()).collect(),
                )
            }
        }
    }
}
impl Name {
    fn unify_freevars_impl(&self) -> Self {
        match self {
            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                let canonical = mettail_runtime::get_or_insert_var(v);
                Name::NVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(canonical)),
                )
            }
            Name::NVar(bound) => Name::NVar(bound.clone()),
            Name::LamProc(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).unify_freevars_impl();
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Name::LamProc(new_scope)
            }
            Name::MLamProc(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).unify_freevars_impl();
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Name::MLamProc(new_scope)
            }
            Name::ApplyProc(f0, f1) => {
                Name::ApplyProc(
                    Box::new((**f0).unify_freevars_impl()),
                    Box::new((**f1).unify_freevars_impl()),
                )
            }
            Name::MApplyProc(f0, f1) => {
                Name::MApplyProc(
                    Box::new((**f0).unify_freevars_impl()),
                    f1.iter().map(|e| e.unify_freevars_impl()).collect(),
                )
            }
            Name::LamName(scope) => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).unify_freevars_impl();
                let new_scope = mettail_runtime::Scope::new(
                    binder.clone(),
                    Box::new(new_body),
                );
                Name::LamName(new_scope)
            }
            Name::MLamName(scope) => {
                let binders = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).unify_freevars_impl();
                let new_scope = mettail_runtime::Scope::new(
                    binders.clone(),
                    Box::new(new_body),
                );
                Name::MLamName(new_scope)
            }
            Name::ApplyName(f0, f1) => {
                Name::ApplyName(
                    Box::new((**f0).unify_freevars_impl()),
                    Box::new((**f1).unify_freevars_impl()),
                )
            }
            Name::MApplyName(f0, f1) => {
                Name::MApplyName(
                    Box::new((**f0).unify_freevars_impl()),
                    f1.iter().map(|e| e.unify_freevars_impl()).collect(),
                )
            }
        }
    }
}
/// Work item for the iterative Display engine.
///
/// Each category variant wraps a raw pointer to a term to be displayed,
/// plus a `min_bp` (minimum binding power) for precedence-aware
/// parenthesization.  When an infix operator's own `left_bp` is less
/// than the inherited `min_bp`, the operator wraps its output in `(…)`.
/// `WriteLiteral` and `WriteString` variants handle static and dynamic
/// text fragments (separators, delimiters, variable names, etc.) that do
/// not require recursive descent into child terms.
#[allow(dead_code)]
enum DisplayTask {
    DisplayProc(*const Proc, u8),
    DisplayName(*const Name, u8),
    /// Write a compile-time-known string (separator, delimiter, keyword).
    WriteLiteral(&'static str),
    /// Write a dynamically computed string (variable name, formatted value).
    WriteString(String),
}
thread_local! {
    #[doc = r" Pool for reusing `DisplayTask` work stacks across Display calls."] #[doc =
    r""] #[doc = r" The `Cell<Vec<DisplayTask>>` pattern allows zero-allocation"] #[doc =
    r" steady-state operation: the first call allocates, subsequent"] #[doc =
    r" calls reuse the same buffer. Re-entrant calls (e.g. from"] #[doc =
    r" collection element formatting) get fresh vectors; the outermost"] #[doc =
    r" call retains capacity."] static DISPLAY_TASK_POOL : std::cell::Cell < Vec <
    DisplayTask >> = std::cell::Cell::new(Vec::new());
}
/// Iterative Display engine.
///
/// Pops tasks from the work stack and either writes text directly to
/// the formatter or pushes sub-tasks for child terms.  Stack-safe for
/// arbitrarily deep terms.
#[allow(dead_code)]
fn display_iterative(
    stack: &mut Vec<DisplayTask>,
    f: &mut std::fmt::Formatter,
) -> std::fmt::Result {
    while let Some(task) = stack.pop() {
        match task {
            DisplayTask::WriteLiteral(s) => {
                f.write_str(s)?;
            }
            DisplayTask::WriteString(s) => {
                f.write_str(&s)?;
            }
            DisplayTask::DisplayProc(ptr, min_bp) => {
                let term = unsafe { &*ptr };
                let _ = min_bp;
                match term {
                    Proc::PZero => {
                        f.write_str("0")?;
                    }
                    Proc::PIn(f1, f3) => {
                        stack.push(DisplayTask::WriteString(")".to_string()));
                        stack.push(DisplayTask::DisplayProc(&**f3 as *const _, 0u8));
                        stack.push(DisplayTask::WriteString(",".to_string()));
                        stack.push(DisplayTask::DisplayName(&**f1 as *const _, 0u8));
                        stack.push(DisplayTask::WriteString("in(".to_string()));
                    }
                    Proc::POut(f1, f3) => {
                        stack.push(DisplayTask::WriteString(")".to_string()));
                        stack.push(DisplayTask::DisplayProc(&**f3 as *const _, 0u8));
                        stack.push(DisplayTask::WriteString(",".to_string()));
                        stack.push(DisplayTask::DisplayName(&**f1 as *const _, 0u8));
                        stack.push(DisplayTask::WriteString("out(".to_string()));
                    }
                    Proc::POpen(f1, f3) => {
                        stack.push(DisplayTask::WriteString(")".to_string()));
                        stack.push(DisplayTask::DisplayProc(&**f3 as *const _, 0u8));
                        stack.push(DisplayTask::WriteString(",".to_string()));
                        stack.push(DisplayTask::DisplayName(&**f1 as *const _, 0u8));
                        stack.push(DisplayTask::WriteString("open(".to_string()));
                    }
                    Proc::PAmb(f0, f2) => {
                        stack.push(DisplayTask::WriteString("]".to_string()));
                        stack.push(DisplayTask::DisplayProc(&**f2 as *const _, 0u8));
                        stack.push(DisplayTask::WriteString("[".to_string()));
                        stack.push(DisplayTask::DisplayName(&**f0 as *const _, 0u8));
                    }
                    Proc::PNew(scope) => {
                        let inner = scope.inner();
                        let binder_name = inner
                            .unsafe_pattern
                            .0
                            .pretty_name
                            .as_ref()
                            .map(|s| s.as_str())
                            .unwrap_or("_");
                        stack.push(DisplayTask::WriteString(")".to_string()));
                        stack
                            .push(
                                DisplayTask::DisplayProc(&*inner.unsafe_body as *const _, 0),
                            );
                        stack.push(DisplayTask::WriteString(" , ".to_string()));
                        stack.push(DisplayTask::WriteString(binder_name.to_string()));
                        stack.push(DisplayTask::WriteString("(".to_string()));
                        stack.push(DisplayTask::WriteString("new".to_string()));
                    }
                    Proc::PPar(f0) => {
                        let mut s = String::from("{");
                        let mut items: Vec<String> = f0
                            .iter()
                            .map(|(elem, count)| {
                                (0..count)
                                    .map(|_| elem.to_string())
                                    .collect::<Vec<_>>()
                                    .join(&format!(" {} ", "|"))
                            })
                            .collect();
                        items.sort();
                        if !items.is_empty() {
                            s.push_str(&items.join(&format!(" {} ", "|")));
                        }
                        s.push_str("}");
                        stack.push(DisplayTask::WriteString(s));
                    }
                    Proc::PVar(var) => {
                        let name = match &var.0 {
                            mettail_runtime::Var::Free(fv) => {
                                fv.pretty_name
                                    .as_ref()
                                    .map(|s| s.to_string())
                                    .unwrap_or_else(|| "_".to_string())
                            }
                            mettail_runtime::Var::Bound(bv) => {
                                bv.pretty_name
                                    .as_ref()
                                    .map(|s| s.to_string())
                                    .unwrap_or_else(|| "_".to_string())
                            }
                        };
                        stack.push(DisplayTask::WriteString(name));
                    }
                    Proc::LamProc(scope) => {
                        let inner = scope.inner();
                        let var_name = inner
                            .unsafe_pattern
                            .0
                            .pretty_name
                            .as_deref()
                            .unwrap_or("?")
                            .to_string();
                        stack.push(DisplayTask::WriteLiteral("}"));
                        stack
                            .push(
                                DisplayTask::DisplayProc(&*inner.unsafe_body as *const _, 0),
                            );
                        stack.push(DisplayTask::WriteLiteral(".{"));
                        stack.push(DisplayTask::WriteString(var_name));
                        stack.push(DisplayTask::WriteLiteral("^"));
                    }
                    Proc::MLamProc(scope) => {
                        let inner = scope.inner();
                        let names: Vec<_> = inner
                            .unsafe_pattern
                            .iter()
                            .map(|b| {
                                b.0.pretty_name.as_deref().unwrap_or("?").to_string()
                            })
                            .collect();
                        stack.push(DisplayTask::WriteLiteral("}"));
                        stack
                            .push(
                                DisplayTask::DisplayProc(&*inner.unsafe_body as *const _, 0),
                            );
                        stack.push(DisplayTask::WriteLiteral("].{"));
                        stack.push(DisplayTask::WriteString(names.join(",")));
                        stack.push(DisplayTask::WriteLiteral("^["));
                    }
                    Proc::ApplyProc(lam, arg) => {
                        stack.push(DisplayTask::WriteLiteral(")"));
                        stack.push(DisplayTask::DisplayProc(&**arg as *const _, 0));
                        stack.push(DisplayTask::WriteLiteral(", "));
                        stack.push(DisplayTask::DisplayProc(&**lam as *const _, 0));
                        stack.push(DisplayTask::WriteString("$proc(".to_string()));
                    }
                    Proc::MApplyProc(lam, args) => {
                        let arg_strs: Vec<_> = args
                            .iter()
                            .map(|a| a.to_string())
                            .collect();
                        let joined = arg_strs.join(", ");
                        stack.push(DisplayTask::WriteLiteral(")"));
                        stack.push(DisplayTask::WriteString(joined));
                        stack.push(DisplayTask::WriteLiteral(", "));
                        stack.push(DisplayTask::DisplayProc(&**lam as *const _, 0));
                        stack.push(DisplayTask::WriteLiteral("("));
                        stack.push(DisplayTask::WriteString("$$proc".to_string()));
                    }
                    Proc::LamName(scope) => {
                        let inner = scope.inner();
                        let var_name = inner
                            .unsafe_pattern
                            .0
                            .pretty_name
                            .as_deref()
                            .unwrap_or("?")
                            .to_string();
                        stack.push(DisplayTask::WriteLiteral("}"));
                        stack
                            .push(
                                DisplayTask::DisplayProc(&*inner.unsafe_body as *const _, 0),
                            );
                        stack.push(DisplayTask::WriteLiteral(".{"));
                        stack.push(DisplayTask::WriteString(var_name));
                        stack.push(DisplayTask::WriteLiteral("^"));
                    }
                    Proc::MLamName(scope) => {
                        let inner = scope.inner();
                        let names: Vec<_> = inner
                            .unsafe_pattern
                            .iter()
                            .map(|b| {
                                b.0.pretty_name.as_deref().unwrap_or("?").to_string()
                            })
                            .collect();
                        stack.push(DisplayTask::WriteLiteral("}"));
                        stack
                            .push(
                                DisplayTask::DisplayProc(&*inner.unsafe_body as *const _, 0),
                            );
                        stack.push(DisplayTask::WriteLiteral("].{"));
                        stack.push(DisplayTask::WriteString(names.join(",")));
                        stack.push(DisplayTask::WriteLiteral("^["));
                    }
                    Proc::ApplyName(lam, arg) => {
                        stack.push(DisplayTask::WriteLiteral(")"));
                        stack.push(DisplayTask::DisplayName(&**arg as *const _, 0));
                        stack.push(DisplayTask::WriteLiteral(", "));
                        stack.push(DisplayTask::DisplayProc(&**lam as *const _, 0));
                        stack.push(DisplayTask::WriteString("$name(".to_string()));
                    }
                    Proc::MApplyName(lam, args) => {
                        let arg_strs: Vec<_> = args
                            .iter()
                            .map(|a| a.to_string())
                            .collect();
                        let joined = arg_strs.join(", ");
                        stack.push(DisplayTask::WriteLiteral(")"));
                        stack.push(DisplayTask::WriteString(joined));
                        stack.push(DisplayTask::WriteLiteral(", "));
                        stack.push(DisplayTask::DisplayProc(&**lam as *const _, 0));
                        stack.push(DisplayTask::WriteLiteral("("));
                        stack.push(DisplayTask::WriteString("$$name".to_string()));
                    }
                }
            }
            DisplayTask::DisplayName(ptr, min_bp) => {
                let term = unsafe { &*ptr };
                let _ = min_bp;
                match term {
                    Name::NVar(var) => {
                        let name = match &var.0 {
                            mettail_runtime::Var::Free(fv) => {
                                fv.pretty_name
                                    .as_ref()
                                    .map(|s| s.to_string())
                                    .unwrap_or_else(|| "_".to_string())
                            }
                            mettail_runtime::Var::Bound(bv) => {
                                bv.pretty_name
                                    .as_ref()
                                    .map(|s| s.to_string())
                                    .unwrap_or_else(|| "_".to_string())
                            }
                        };
                        stack.push(DisplayTask::WriteString(name));
                    }
                    Name::LamProc(scope) => {
                        let inner = scope.inner();
                        let var_name = inner
                            .unsafe_pattern
                            .0
                            .pretty_name
                            .as_deref()
                            .unwrap_or("?")
                            .to_string();
                        stack.push(DisplayTask::WriteLiteral("}"));
                        stack
                            .push(
                                DisplayTask::DisplayName(&*inner.unsafe_body as *const _, 0),
                            );
                        stack.push(DisplayTask::WriteLiteral(".{"));
                        stack.push(DisplayTask::WriteString(var_name));
                        stack.push(DisplayTask::WriteLiteral("^"));
                    }
                    Name::MLamProc(scope) => {
                        let inner = scope.inner();
                        let names: Vec<_> = inner
                            .unsafe_pattern
                            .iter()
                            .map(|b| {
                                b.0.pretty_name.as_deref().unwrap_or("?").to_string()
                            })
                            .collect();
                        stack.push(DisplayTask::WriteLiteral("}"));
                        stack
                            .push(
                                DisplayTask::DisplayName(&*inner.unsafe_body as *const _, 0),
                            );
                        stack.push(DisplayTask::WriteLiteral("].{"));
                        stack.push(DisplayTask::WriteString(names.join(",")));
                        stack.push(DisplayTask::WriteLiteral("^["));
                    }
                    Name::ApplyProc(lam, arg) => {
                        stack.push(DisplayTask::WriteLiteral(")"));
                        stack.push(DisplayTask::DisplayProc(&**arg as *const _, 0));
                        stack.push(DisplayTask::WriteLiteral(", "));
                        stack.push(DisplayTask::DisplayName(&**lam as *const _, 0));
                        stack.push(DisplayTask::WriteString("$proc(".to_string()));
                    }
                    Name::MApplyProc(lam, args) => {
                        let arg_strs: Vec<_> = args
                            .iter()
                            .map(|a| a.to_string())
                            .collect();
                        let joined = arg_strs.join(", ");
                        stack.push(DisplayTask::WriteLiteral(")"));
                        stack.push(DisplayTask::WriteString(joined));
                        stack.push(DisplayTask::WriteLiteral(", "));
                        stack.push(DisplayTask::DisplayName(&**lam as *const _, 0));
                        stack.push(DisplayTask::WriteLiteral("("));
                        stack.push(DisplayTask::WriteString("$$proc".to_string()));
                    }
                    Name::LamName(scope) => {
                        let inner = scope.inner();
                        let var_name = inner
                            .unsafe_pattern
                            .0
                            .pretty_name
                            .as_deref()
                            .unwrap_or("?")
                            .to_string();
                        stack.push(DisplayTask::WriteLiteral("}"));
                        stack
                            .push(
                                DisplayTask::DisplayName(&*inner.unsafe_body as *const _, 0),
                            );
                        stack.push(DisplayTask::WriteLiteral(".{"));
                        stack.push(DisplayTask::WriteString(var_name));
                        stack.push(DisplayTask::WriteLiteral("^"));
                    }
                    Name::MLamName(scope) => {
                        let inner = scope.inner();
                        let names: Vec<_> = inner
                            .unsafe_pattern
                            .iter()
                            .map(|b| {
                                b.0.pretty_name.as_deref().unwrap_or("?").to_string()
                            })
                            .collect();
                        stack.push(DisplayTask::WriteLiteral("}"));
                        stack
                            .push(
                                DisplayTask::DisplayName(&*inner.unsafe_body as *const _, 0),
                            );
                        stack.push(DisplayTask::WriteLiteral("].{"));
                        stack.push(DisplayTask::WriteString(names.join(",")));
                        stack.push(DisplayTask::WriteLiteral("^["));
                    }
                    Name::ApplyName(lam, arg) => {
                        stack.push(DisplayTask::WriteLiteral(")"));
                        stack.push(DisplayTask::DisplayName(&**arg as *const _, 0));
                        stack.push(DisplayTask::WriteLiteral(", "));
                        stack.push(DisplayTask::DisplayName(&**lam as *const _, 0));
                        stack.push(DisplayTask::WriteString("$name(".to_string()));
                    }
                    Name::MApplyName(lam, args) => {
                        let arg_strs: Vec<_> = args
                            .iter()
                            .map(|a| a.to_string())
                            .collect();
                        let joined = arg_strs.join(", ");
                        stack.push(DisplayTask::WriteLiteral(")"));
                        stack.push(DisplayTask::WriteString(joined));
                        stack.push(DisplayTask::WriteLiteral(", "));
                        stack.push(DisplayTask::DisplayName(&**lam as *const _, 0));
                        stack.push(DisplayTask::WriteLiteral("("));
                        stack.push(DisplayTask::WriteString("$$name".to_string()));
                    }
                }
            }
        }
    }
    Ok(())
}
impl std::fmt::Display for Proc {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let result = DISPLAY_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                stack.clear();
                stack.push(DisplayTask::DisplayProc(self as *const Proc, 0));
                let result = display_iterative(&mut stack, f);
                cell.set(stack);
                result
            });
        match result {
            Ok(fmt_result) => fmt_result,
            Err(_) => {
                let mut stack = Vec::new();
                stack.push(DisplayTask::DisplayProc(self as *const Proc, 0));
                display_iterative(&mut stack, f)
            }
        }
    }
}
impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let result = DISPLAY_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                stack.clear();
                stack.push(DisplayTask::DisplayName(self as *const Name, 0));
                let result = display_iterative(&mut stack, f);
                cell.set(stack);
                result
            });
        match result {
            Ok(fmt_result) => fmt_result,
            Err(_) => {
                let mut stack = Vec::new();
                stack.push(DisplayTask::DisplayName(self as *const Name, 0));
                display_iterative(&mut stack, f)
            }
        }
    }
}
struct GenerationContext {
    vars: Vec<String>,
    initial_var_count: usize,
    max_depth: usize,
    max_collection_width: usize,
    proc_by_depth: std::collections::HashMap<usize, Vec<Proc>>,
    name_by_depth: std::collections::HashMap<usize, Vec<Name>>,
}
impl GenerationContext {
    fn new(vars: Vec<String>, max_depth: usize, max_collection_width: usize) -> Self {
        let initial_var_count = vars.len();
        Self {
            vars,
            initial_var_count,
            max_depth,
            max_collection_width,
            proc_by_depth: std::collections::HashMap::new(),
            name_by_depth: std::collections::HashMap::new(),
        }
    }
    fn new_with_extended_vars(
        vars: Vec<String>,
        initial_var_count: usize,
        max_depth: usize,
        max_collection_width: usize,
    ) -> Self {
        Self {
            vars,
            initial_var_count,
            max_depth,
            max_collection_width,
            proc_by_depth: std::collections::HashMap::new(),
            name_by_depth: std::collections::HashMap::new(),
        }
    }
    fn generate_all(mut self) -> Self {
        for depth in 0..=self.max_depth {
            self.generate_proc(depth);
            self.generate_name(depth);
        }
        self
    }
    fn generate_proc(&mut self, depth: usize) {
        let mut terms: Vec<Proc> = Vec::new();
        if depth == 0 {
            terms.push(Proc::PZero);
        } else {
            for d1 in 0..depth {
                for d2 in 0..depth {
                    if d1.max(d2) + 1 == depth {
                        if let Some(args1) = self.name_by_depth.get(&d1) {
                            if let Some(args2) = self.proc_by_depth.get(&d2) {
                                for arg1 in args1 {
                                    for arg2 in args2 {
                                        terms
                                            .push(
                                                Proc::PIn(Box::new(arg1.clone()), Box::new(arg2.clone())),
                                            );
                                    }
                                }
                            }
                        }
                    }
                }
            }
            for d1 in 0..depth {
                for d2 in 0..depth {
                    if d1.max(d2) + 1 == depth {
                        if let Some(args1) = self.name_by_depth.get(&d1) {
                            if let Some(args2) = self.proc_by_depth.get(&d2) {
                                for arg1 in args1 {
                                    for arg2 in args2 {
                                        terms
                                            .push(
                                                Proc::POut(Box::new(arg1.clone()), Box::new(arg2.clone())),
                                            );
                                    }
                                }
                            }
                        }
                    }
                }
            }
            for d1 in 0..depth {
                for d2 in 0..depth {
                    if d1.max(d2) + 1 == depth {
                        if let Some(args1) = self.name_by_depth.get(&d1) {
                            if let Some(args2) = self.proc_by_depth.get(&d2) {
                                for arg1 in args1 {
                                    for arg2 in args2 {
                                        terms
                                            .push(
                                                Proc::POpen(Box::new(arg1.clone()), Box::new(arg2.clone())),
                                            );
                                    }
                                }
                            }
                        }
                    }
                }
            }
            for d1 in 0..depth {
                for d2 in 0..depth {
                    if d1.max(d2) + 1 == depth {
                        if let Some(args1) = self.name_by_depth.get(&d1) {
                            if let Some(args2) = self.proc_by_depth.get(&d2) {
                                for arg1 in args1 {
                                    for arg2 in args2 {
                                        terms
                                            .push(
                                                Proc::PAmb(Box::new(arg1.clone()), Box::new(arg2.clone())),
                                            );
                                    }
                                }
                            }
                        }
                    }
                }
            }
            let current_binding_depth = self.vars.len() - self.initial_var_count;
            let binder_name = format!("x{}", current_binding_depth);
            let mut extended_vars = self.vars.clone();
            extended_vars.push(binder_name.clone());
            let mut temp_ctx = GenerationContext::new_with_extended_vars(
                extended_vars,
                self.initial_var_count,
                depth - 1,
                self.max_collection_width,
            );
            temp_ctx = temp_ctx.generate_all();
            let mut bodies_with_binder = Vec::new();
            for d in 0..depth {
                if let Some(ts) = temp_ctx.proc_by_depth.get(&d) {
                    bodies_with_binder.extend(ts.clone());
                }
            }
            for body in bodies_with_binder {
                let binder_var = mettail_runtime::get_or_create_var(&binder_name);
                let binder = mettail_runtime::Binder(binder_var);
                let scope = mettail_runtime::Scope::new(binder, Box::new(body));
                terms.push(Proc::PNew(scope));
            }
            for size in 0..=self.max_collection_width {
                if size == 0 {
                    let bag = mettail_runtime::HashBag::new();
                    terms.push(Proc::PPar(bag));
                } else if size == 1 {
                    for d in 0..depth {
                        if let Some(elems) = self.proc_by_depth.get(&d) {
                            for elem in elems {
                                let mut bag = mettail_runtime::HashBag::new();
                                bag.insert(elem.clone());
                                terms.push(Proc::PPar(bag));
                            }
                        }
                    }
                } else if size == 2 {
                    for d1 in 0..depth {
                        for d2 in 0..depth {
                            if let Some(elems1) = self.proc_by_depth.get(&d1) {
                                if let Some(elems2) = self.proc_by_depth.get(&d2) {
                                    for elem1 in elems1 {
                                        for elem2 in elems2 {
                                            let mut bag = mettail_runtime::HashBag::new();
                                            bag.insert(elem1.clone());
                                            bag.insert(elem2.clone());
                                            terms.push(Proc::PPar(bag));
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else if size == 3 {
                    for d1 in 0..depth {
                        for d2 in 0..depth {
                            for d3 in 0..depth {
                                if let Some(elems1) = self.proc_by_depth.get(&d1) {
                                    if let Some(elems2) = self.proc_by_depth.get(&d2) {
                                        if let Some(elems3) = self.proc_by_depth.get(&d3) {
                                            for elem1 in elems1 {
                                                for elem2 in elems2 {
                                                    for elem3 in elems3 {
                                                        let mut bag = mettail_runtime::HashBag::new();
                                                        bag.insert(elem1.clone());
                                                        bag.insert(elem2.clone());
                                                        bag.insert(elem3.clone());
                                                        terms.push(Proc::PPar(bag));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {}
            }
        }
        terms.sort();
        terms.dedup();
        self.proc_by_depth.insert(depth, terms);
    }
    fn generate_name(&mut self, depth: usize) {
        let mut terms: Vec<Name> = Vec::new();
        if depth == 0 {} else {}
        terms.sort();
        terms.dedup();
        self.name_by_depth.insert(depth, terms);
    }
}
impl Proc {
    /// Generate all terms up to max_depth
    ///
    /// # Arguments
    /// * `vars` - Pool of variable names for free variables
    /// * `max_depth` - Maximum operator nesting level
    /// * `max_collection_width` - Maximum number of elements in any collection
    ///
    /// # Returns
    /// Sorted, deduplicated vector of terms
    ///
    /// # Warning
    /// Number of terms grows exponentially with depth and collection width!
    /// Recommend max_depth <= 3 and max_collection_width <= 2 for exhaustive generation.
    pub fn generate_terms(
        vars: &[String],
        max_depth: usize,
        max_collection_width: usize,
    ) -> Vec<Proc> {
        let ctx = GenerationContext::new(vars.to_vec(), max_depth, max_collection_width);
        let ctx = ctx.generate_all();
        let mut all_terms = Vec::new();
        for depth in 0..=max_depth {
            if let Some(terms) = ctx.proc_by_depth.get(&depth) {
                all_terms.extend(terms.clone());
            }
        }
        all_terms.sort();
        all_terms.dedup();
        all_terms
    }
}
impl Name {
    /// Generate all terms up to max_depth
    ///
    /// # Arguments
    /// * `vars` - Pool of variable names for free variables
    /// * `max_depth` - Maximum operator nesting level
    /// * `max_collection_width` - Maximum number of elements in any collection
    ///
    /// # Returns
    /// Sorted, deduplicated vector of terms
    ///
    /// # Warning
    /// Number of terms grows exponentially with depth and collection width!
    /// Recommend max_depth <= 3 and max_collection_width <= 2 for exhaustive generation.
    pub fn generate_terms(
        vars: &[String],
        max_depth: usize,
        max_collection_width: usize,
    ) -> Vec<Name> {
        let ctx = GenerationContext::new(vars.to_vec(), max_depth, max_collection_width);
        let ctx = ctx.generate_all();
        let mut all_terms = Vec::new();
        for depth in 0..=max_depth {
            if let Some(terms) = ctx.name_by_depth.get(&depth) {
                all_terms.extend(terms.clone());
            }
        }
        all_terms.sort();
        all_terms.dedup();
        all_terms
    }
}
impl Proc {
    /// Generate a random term at exactly the given depth
    ///
    /// # Arguments
    /// * `vars` - Pool of variable names for free variables
    /// * `depth` - Target depth (operator nesting level)
    /// * `max_collection_width` - Maximum number of elements in any collection
    ///
    /// # Example
    /// ```ignore
    /// let term = Proc::generate_random_at_depth(&["a".into(), "b".into()], 25, 3);
    /// ```
    pub fn generate_random_at_depth(
        vars: &[String],
        depth: usize,
        max_collection_width: usize,
    ) -> Self {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        Self::generate_random_at_depth_internal(
            vars,
            depth,
            max_collection_width,
            &mut rng,
            0,
        )
    }
    /// Generate a random term at exactly the given depth with a seed
    ///
    /// This is deterministic - same seed produces same term.
    ///
    /// # Arguments
    /// * `vars` - Pool of variable names for free variables
    /// * `depth` - Target depth (operator nesting level)
    /// * `max_collection_width` - Maximum number of elements in any collection
    /// * `seed` - Random seed for reproducibility
    pub fn generate_random_at_depth_with_seed(
        vars: &[String],
        depth: usize,
        max_collection_width: usize,
        seed: u64,
    ) -> Self {
        use rand::{SeedableRng, Rng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        Self::generate_random_at_depth_internal(
            vars,
            depth,
            max_collection_width,
            &mut rng,
            0,
        )
    }
    fn generate_random_at_depth_internal<R: rand::Rng>(
        vars: &[String],
        depth: usize,
        max_collection_width: usize,
        rng: &mut R,
        binding_depth: usize,
    ) -> Self {
        if depth == 0 {
            Proc::PZero
        } else {
            {
                let choice = rng.gen_range(0..6usize);
                match choice {
                    0usize => {
                        let d1 = rng.gen_range(0..depth);
                        let d2 = if d1 == depth - 1 {
                            rng.gen_range(0..depth)
                        } else {
                            depth - 1
                        };
                        let arg1 = Name::generate_random_at_depth_internal(
                            vars,
                            d1,
                            max_collection_width,
                            rng,
                            binding_depth,
                        );
                        let arg2 = Proc::generate_random_at_depth_internal(
                            vars,
                            d2,
                            max_collection_width,
                            rng,
                            binding_depth,
                        );
                        Proc::PIn(Box::new(arg1), Box::new(arg2))
                    }
                    1usize => {
                        let d1 = rng.gen_range(0..depth);
                        let d2 = if d1 == depth - 1 {
                            rng.gen_range(0..depth)
                        } else {
                            depth - 1
                        };
                        let arg1 = Name::generate_random_at_depth_internal(
                            vars,
                            d1,
                            max_collection_width,
                            rng,
                            binding_depth,
                        );
                        let arg2 = Proc::generate_random_at_depth_internal(
                            vars,
                            d2,
                            max_collection_width,
                            rng,
                            binding_depth,
                        );
                        Proc::POut(Box::new(arg1), Box::new(arg2))
                    }
                    2usize => {
                        let d1 = rng.gen_range(0..depth);
                        let d2 = if d1 == depth - 1 {
                            rng.gen_range(0..depth)
                        } else {
                            depth - 1
                        };
                        let arg1 = Name::generate_random_at_depth_internal(
                            vars,
                            d1,
                            max_collection_width,
                            rng,
                            binding_depth,
                        );
                        let arg2 = Proc::generate_random_at_depth_internal(
                            vars,
                            d2,
                            max_collection_width,
                            rng,
                            binding_depth,
                        );
                        Proc::POpen(Box::new(arg1), Box::new(arg2))
                    }
                    3usize => {
                        let d1 = rng.gen_range(0..depth);
                        let d2 = if d1 == depth - 1 {
                            rng.gen_range(0..depth)
                        } else {
                            depth - 1
                        };
                        let arg1 = Name::generate_random_at_depth_internal(
                            vars,
                            d1,
                            max_collection_width,
                            rng,
                            binding_depth,
                        );
                        let arg2 = Proc::generate_random_at_depth_internal(
                            vars,
                            d2,
                            max_collection_width,
                            rng,
                            binding_depth,
                        );
                        Proc::PAmb(Box::new(arg1), Box::new(arg2))
                    }
                    4usize => {
                        let binder_name = format!("x{}", binding_depth);
                        let mut extended_vars = vars.to_vec();
                        extended_vars.push(binder_name.clone());
                        let body = Proc::generate_random_at_depth_internal(
                            &extended_vars,
                            depth - 1,
                            max_collection_width,
                            rng,
                            binding_depth + 1,
                        );
                        let binder_var = mettail_runtime::get_or_create_var(
                            &binder_name,
                        );
                        let binder = mettail_runtime::Binder(binder_var);
                        let scope = mettail_runtime::Scope::new(binder, Box::new(body));
                        Proc::PNew(scope)
                    }
                    5usize => {
                        let size = rng.gen_range(0..=max_collection_width);
                        let mut bag = mettail_runtime::HashBag::new();
                        for _ in 0..size {
                            let elem_depth = if depth > 0 {
                                rng.gen_range(0..depth)
                            } else {
                                0
                            };
                            let elem = Proc::generate_random_at_depth_internal(
                                vars,
                                elem_depth,
                                max_collection_width,
                                rng,
                                binding_depth,
                            );
                            bag.insert(elem);
                        }
                        Proc::PPar(bag)
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
impl Name {
    /// Generate a random term at exactly the given depth
    ///
    /// # Arguments
    /// * `vars` - Pool of variable names for free variables
    /// * `depth` - Target depth (operator nesting level)
    /// * `max_collection_width` - Maximum number of elements in any collection
    ///
    /// # Example
    /// ```ignore
    /// let term = Proc::generate_random_at_depth(&["a".into(), "b".into()], 25, 3);
    /// ```
    pub fn generate_random_at_depth(
        vars: &[String],
        depth: usize,
        max_collection_width: usize,
    ) -> Self {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        Self::generate_random_at_depth_internal(
            vars,
            depth,
            max_collection_width,
            &mut rng,
            0,
        )
    }
    /// Generate a random term at exactly the given depth with a seed
    ///
    /// This is deterministic - same seed produces same term.
    ///
    /// # Arguments
    /// * `vars` - Pool of variable names for free variables
    /// * `depth` - Target depth (operator nesting level)
    /// * `max_collection_width` - Maximum number of elements in any collection
    /// * `seed` - Random seed for reproducibility
    pub fn generate_random_at_depth_with_seed(
        vars: &[String],
        depth: usize,
        max_collection_width: usize,
        seed: u64,
    ) -> Self {
        use rand::{SeedableRng, Rng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        Self::generate_random_at_depth_internal(
            vars,
            depth,
            max_collection_width,
            &mut rng,
            0,
        )
    }
    fn generate_random_at_depth_internal<R: rand::Rng>(
        vars: &[String],
        depth: usize,
        max_collection_width: usize,
        rng: &mut R,
        binding_depth: usize,
    ) -> Self {
        if depth == 0 {
            panic!("No depth 0 constructors for {}", stringify!(Name))
        } else {
            panic!("No depth 0 constructors for {}", stringify!(Name))
        }
    }
}
impl Proc {
    /// Returns `true` if this term contains no free variables.
    ///
    /// A ground term is fully concrete — all leaf positions are
    /// literals or nullary constructors. Bound variables (inside
    /// `Scope`) do not make a term non-ground.
    pub fn is_ground(&self) -> bool {
        match self {
            Proc::PZero => true,
            Proc::PIn(f0, f1) => f0.is_ground() && f1.is_ground(),
            Proc::POut(f0, f1) => f0.is_ground() && f1.is_ground(),
            Proc::POpen(f0, f1) => f0.is_ground() && f1.is_ground(),
            Proc::PAmb(f0, f1) => f0.is_ground() && f1.is_ground(),
            Proc::PNew(scope) => scope.inner().unsafe_body.is_ground(),
            Proc::PPar(coll) => coll.iter().all(|(x, _count)| x.is_ground()),
            Proc::PVar(_) => false,
            Proc::LamProc(scope) => scope.inner().unsafe_body.is_ground(),
            Proc::MLamProc(scope) => scope.inner().unsafe_body.is_ground(),
            Proc::ApplyProc(f0, f1) => f0.is_ground() && f1.is_ground(),
            Proc::MApplyProc(f0, f1) => {
                f0.is_ground() && f1.iter().all(|x| x.is_ground())
            }
            Proc::LamName(scope) => scope.inner().unsafe_body.is_ground(),
            Proc::MLamName(scope) => scope.inner().unsafe_body.is_ground(),
            Proc::ApplyName(f0, f1) => f0.is_ground() && f1.is_ground(),
            Proc::MApplyName(f0, f1) => {
                f0.is_ground() && f1.iter().all(|x| x.is_ground())
            }
        }
    }
}
impl Name {
    /// Returns `true` if this term contains no free variables.
    ///
    /// A ground term is fully concrete — all leaf positions are
    /// literals or nullary constructors. Bound variables (inside
    /// `Scope`) do not make a term non-ground.
    pub fn is_ground(&self) -> bool {
        match self {
            Name::NVar(_) => false,
            Name::LamProc(scope) => scope.inner().unsafe_body.is_ground(),
            Name::MLamProc(scope) => scope.inner().unsafe_body.is_ground(),
            Name::ApplyProc(f0, f1) => f0.is_ground() && f1.is_ground(),
            Name::MApplyProc(f0, f1) => {
                f0.is_ground() && f1.iter().all(|x| x.is_ground())
            }
            Name::LamName(scope) => scope.inner().unsafe_body.is_ground(),
            Name::MLamName(scope) => scope.inner().unsafe_body.is_ground(),
            Name::ApplyName(f0, f1) => f0.is_ground() && f1.is_ground(),
            Name::MApplyName(f0, f1) => {
                f0.is_ground() && f1.iter().all(|x| x.is_ground())
            }
        }
    }
}
impl Proc {
    /// Compute the maximum nesting depth of this term.
    ///
    /// - Leaves (variables, literals, nullary constructors): 0
    /// - Constructors: 1 + max(child depths)
    /// - Collections: 1 + max(element depths)
    /// - Binders: 1 + max(pre-scope fields, body)
    ///
    /// Used by A-RT05 post-fixpoint convergence check.
    pub fn term_depth(&self) -> u32 {
        match self {
            Proc::PZero => 0,
            Proc::PIn(f0, f1) => 1 + (f0.term_depth()).max(f1.term_depth()),
            Proc::POut(f0, f1) => 1 + (f0.term_depth()).max(f1.term_depth()),
            Proc::POpen(f0, f1) => 1 + (f0.term_depth()).max(f1.term_depth()),
            Proc::PAmb(f0, f1) => 1 + (f0.term_depth()).max(f1.term_depth()),
            Proc::PNew(scope) => 1 + scope.inner().unsafe_body.term_depth(),
            Proc::PPar(coll) => {
                1 + coll.iter().map(|(x, _count)| x.term_depth()).max().unwrap_or(0)
            }
            Proc::PVar(_) => 0,
            Proc::LamProc(scope) => 1 + scope.inner().unsafe_body.term_depth(),
            Proc::MLamProc(scope) => 1 + scope.inner().unsafe_body.term_depth(),
            Proc::ApplyProc(f0, f1) => 1 + (f0.term_depth()).max(f1.term_depth()),
            Proc::MApplyProc(f0, f1) => {
                1
                    + (f0.term_depth())
                        .max(f1.iter().map(|x| x.term_depth()).max().unwrap_or(0))
            }
            Proc::LamName(scope) => 1 + scope.inner().unsafe_body.term_depth(),
            Proc::MLamName(scope) => 1 + scope.inner().unsafe_body.term_depth(),
            Proc::ApplyName(f0, f1) => 1 + (f0.term_depth()).max(f1.term_depth()),
            Proc::MApplyName(f0, f1) => {
                1
                    + (f0.term_depth())
                        .max(f1.iter().map(|x| x.term_depth()).max().unwrap_or(0))
            }
        }
    }
}
impl Name {
    /// Compute the maximum nesting depth of this term.
    ///
    /// - Leaves (variables, literals, nullary constructors): 0
    /// - Constructors: 1 + max(child depths)
    /// - Collections: 1 + max(element depths)
    /// - Binders: 1 + max(pre-scope fields, body)
    ///
    /// Used by A-RT05 post-fixpoint convergence check.
    pub fn term_depth(&self) -> u32 {
        match self {
            Name::NVar(_) => 0,
            Name::LamProc(scope) => 1 + scope.inner().unsafe_body.term_depth(),
            Name::MLamProc(scope) => 1 + scope.inner().unsafe_body.term_depth(),
            Name::ApplyProc(f0, f1) => 1 + (f0.term_depth()).max(f1.term_depth()),
            Name::MApplyProc(f0, f1) => {
                1
                    + (f0.term_depth())
                        .max(f1.iter().map(|x| x.term_depth()).max().unwrap_or(0))
            }
            Name::LamName(scope) => 1 + scope.inner().unsafe_body.term_depth(),
            Name::MLamName(scope) => 1 + scope.inner().unsafe_body.term_depth(),
            Name::ApplyName(f0, f1) => 1 + (f0.term_depth()).max(f1.term_depth()),
            Name::MApplyName(f0, f1) => {
                1
                    + (f0.term_depth())
                        .max(f1.iter().map(|x| x.term_depth()).max().unwrap_or(0))
            }
        }
    }
}
/// Bindings collected during first-order pattern matching.
///
/// Accumulates variable bindings from cross-category matching.
/// Each category has its own binding vector to support typed lookups.
#[derive(Debug, Clone)]
pub struct MatchBindings {
    pub proc_bindings: Vec<(String, Proc)>,
    pub name_bindings: Vec<(String, Name)>,
}
impl MatchBindings {
    /// Create empty bindings (no variables matched).
    pub fn empty() -> Self {
        MatchBindings {
            proc_bindings: Vec::new(),
            name_bindings: Vec::new(),
        }
    }
    /// Create bindings with a single binding for this category.
    pub fn proc(var_name: String, val: Proc) -> Self {
        MatchBindings {
            proc_bindings: vec![(var_name, val)],
            name_bindings: Vec::new(),
        }
    }
    /// Create bindings with a single binding for this category.
    pub fn name(var_name: String, val: Name) -> Self {
        MatchBindings {
            name_bindings: vec![(var_name, val)],
            proc_bindings: Vec::new(),
        }
    }
    /// Merge another set of bindings into this one.
    pub fn merge(&mut self, other: MatchBindings) {
        self.proc_bindings.extend(other.proc_bindings);
        self.name_bindings.extend(other.name_bindings);
    }
    /// Look up a variable binding in this category by name.
    pub fn get_proc(&self, var_name: &str) -> Option<&Proc> {
        self.proc_bindings.iter().find(|(name, _)| name == var_name).map(|(_, val)| val)
    }
    /// Look up a variable binding in this category by name.
    pub fn get_name(&self, var_name: &str) -> Option<&Name> {
        self.name_bindings.iter().find(|(name, _)| name == var_name).map(|(_, val)| val)
    }
}
/// Work item for the iterative match_pattern engine.
///
/// Each variant wraps a `(ground, pattern)` pair for one category.
/// The iterative engine pops tasks from a `Vec<MatchTask>` work stack,
/// processes each one (binding variables, checking equality, or pushing
/// sub-field tasks), and accumulates bindings until the stack is empty
/// (success) or a constructor clash is detected (failure).
#[allow(dead_code)]
enum MatchTask {
    /// Match a #cat ground term against a #cat pattern.
    MatchProc(Proc, Proc),
    /// Match a #cat ground term against a #cat pattern.
    MatchName(Name, Name),
}
thread_local! {
    #[doc = r" Pool for reusing `MatchTask` work stacks across calls."] #[doc = r""]
    #[doc = r" The `Cell<Vec<MatchTask>>` pattern allows zero-allocation"] #[doc =
    r" steady-state operation: the first call allocates, subsequent"] #[doc =
    r" calls reuse the same buffer. Re-entrant calls (from Collection"] #[doc =
    r" matching) get fresh vectors; the outermost call retains capacity."] static
    MATCH_TASK_POOL : std::cell::Cell < Vec < MatchTask >> =
    std::cell::Cell::new(Vec::new());
}
/// Iterative match pattern engine.
///
/// Processes the work stack until empty (success) or a constructor
/// clash is detected (failure). Stack-safe for arbitrarily deep terms.
#[allow(dead_code)]
fn match_pattern_iterative(stack: &mut Vec<MatchTask>) -> Option<MatchBindings> {
    let mut bindings = MatchBindings::empty();
    while let Some(task) = stack.pop() {
        match task {
            MatchTask::MatchProc(ground, pattern) => {
                if let Proc::PVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)),
                ) = pattern {
                    if let Some(ref pretty_name) = fv.pretty_name {
                        bindings
                            .merge(
                                MatchBindings::proc(pretty_name.clone(), ground.clone()),
                            );
                        continue;
                    }
                }
                match (&ground, &pattern) {
                    (Proc::PZero, Proc::PZero) => {}
                    (Proc::PIn(g0, g1), Proc::PIn(p0, p1)) => {
                        stack.push(MatchTask::MatchProc((**g1).clone(), (**p1).clone()));
                        stack.push(MatchTask::MatchName((**g0).clone(), (**p0).clone()));
                    }
                    (Proc::POut(g0, g1), Proc::POut(p0, p1)) => {
                        stack.push(MatchTask::MatchProc((**g1).clone(), (**p1).clone()));
                        stack.push(MatchTask::MatchName((**g0).clone(), (**p0).clone()));
                    }
                    (Proc::POpen(g0, g1), Proc::POpen(p0, p1)) => {
                        stack.push(MatchTask::MatchProc((**g1).clone(), (**p1).clone()));
                        stack.push(MatchTask::MatchName((**g0).clone(), (**p0).clone()));
                    }
                    (Proc::PAmb(g0, g1), Proc::PAmb(p0, p1)) => {
                        stack.push(MatchTask::MatchProc((**g1).clone(), (**p1).clone()));
                        stack.push(MatchTask::MatchName((**g0).clone(), (**p0).clone()));
                    }
                    (Proc::PNew(g0), Proc::PNew(p0)) => {
                        let g_inner = g0.inner();
                        let p_inner = p0.inner();
                        let body_match = (*g_inner.unsafe_body)
                            .match_pattern(&*p_inner.unsafe_body);
                        match body_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                    (Proc::PPar(g_bag), Proc::PPar(p_bag)) => {
                        let g_elems: Vec<_> = g_bag
                            .iter()
                            .flat_map(|(elem, count)| {
                                std::iter::repeat(elem.clone()).take(count)
                            })
                            .collect();
                        let p_elems: Vec<_> = p_bag
                            .iter()
                            .flat_map(|(elem, count)| {
                                std::iter::repeat(elem.clone()).take(count)
                            })
                            .collect();
                        let mut claimed = vec![false; g_elems.len()];
                        for p_elem in &p_elems {
                            let is_var = matches!(
                                p_elem,
                                Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(_)))
                            );
                            if is_var {
                                if let Some(idx) = claimed.iter().position(|c| !c) {
                                    claimed[idx] = true;
                                    if let Proc::PVar(
                                        mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)),
                                    ) = p_elem {
                                        if let Some(ref pretty_name) = fv.pretty_name {
                                            let sub = p_elem.match_pattern(&g_elems[idx]);
                                            if let Some(b) = sub {
                                                bindings.merge(b);
                                            }
                                        }
                                    }
                                } else {
                                    return None;
                                }
                            } else {
                                let found = g_elems
                                    .iter()
                                    .enumerate()
                                    .find(|(idx, g_elem)| {
                                        !claimed[*idx] && g_elem.match_pattern(p_elem).is_some()
                                    });
                                match found {
                                    Some((idx, _)) => {
                                        claimed[idx] = true;
                                        if let Some(b) = g_elems[idx].match_pattern(p_elem) {
                                            bindings.merge(b);
                                        }
                                    }
                                    None => return None,
                                }
                            }
                        }
                    }
                    (Proc::PVar(v1), Proc::PVar(v2)) if v1 == v2 => {}
                    (Proc::LamProc(g0), Proc::LamProc(p0)) => {
                        let g_inner = g0.inner();
                        let p_inner = p0.inner();
                        let body_match = (*g_inner.unsafe_body)
                            .match_pattern(&*p_inner.unsafe_body);
                        match body_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                    (Proc::MLamProc(g0), Proc::MLamProc(p0)) => {
                        let g_inner = g0.inner();
                        let p_inner = p0.inner();
                        if g_inner.unsafe_pattern.len() != p_inner.unsafe_pattern.len() {
                            return None;
                        }
                        let body_match = (*g_inner.unsafe_body)
                            .match_pattern(&*p_inner.unsafe_body);
                        match body_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                    (Proc::ApplyProc(g0, g1), Proc::ApplyProc(p0, p1)) => {
                        stack.push(MatchTask::MatchProc((**g1).clone(), (**p1).clone()));
                        stack.push(MatchTask::MatchProc((**g0).clone(), (**p0).clone()));
                    }
                    (Proc::MApplyProc(_, _), Proc::MApplyProc(_, _)) => return None,
                    (Proc::LamName(g0), Proc::LamName(p0)) => {
                        let g_inner = g0.inner();
                        let p_inner = p0.inner();
                        let body_match = (*g_inner.unsafe_body)
                            .match_pattern(&*p_inner.unsafe_body);
                        match body_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                    (Proc::MLamName(g0), Proc::MLamName(p0)) => {
                        let g_inner = g0.inner();
                        let p_inner = p0.inner();
                        if g_inner.unsafe_pattern.len() != p_inner.unsafe_pattern.len() {
                            return None;
                        }
                        let body_match = (*g_inner.unsafe_body)
                            .match_pattern(&*p_inner.unsafe_body);
                        match body_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                    (Proc::ApplyName(g0, g1), Proc::ApplyName(p0, p1)) => {
                        stack.push(MatchTask::MatchName((**g1).clone(), (**p1).clone()));
                        stack.push(MatchTask::MatchProc((**g0).clone(), (**p0).clone()));
                    }
                    (Proc::MApplyName(_, _), Proc::MApplyName(_, _)) => return None,
                    _ => return None,
                }
            }
            MatchTask::MatchName(ground, pattern) => {
                if let Name::NVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)),
                ) = pattern {
                    if let Some(ref pretty_name) = fv.pretty_name {
                        bindings
                            .merge(
                                MatchBindings::name(pretty_name.clone(), ground.clone()),
                            );
                        continue;
                    }
                }
                match (&ground, &pattern) {
                    (Name::NVar(v1), Name::NVar(v2)) if v1 == v2 => {}
                    (Name::LamProc(g0), Name::LamProc(p0)) => {
                        let g_inner = g0.inner();
                        let p_inner = p0.inner();
                        let body_match = (*g_inner.unsafe_body)
                            .match_pattern(&*p_inner.unsafe_body);
                        match body_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                    (Name::MLamProc(g0), Name::MLamProc(p0)) => {
                        let g_inner = g0.inner();
                        let p_inner = p0.inner();
                        if g_inner.unsafe_pattern.len() != p_inner.unsafe_pattern.len() {
                            return None;
                        }
                        let body_match = (*g_inner.unsafe_body)
                            .match_pattern(&*p_inner.unsafe_body);
                        match body_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                    (Name::ApplyProc(g0, g1), Name::ApplyProc(p0, p1)) => {
                        stack.push(MatchTask::MatchProc((**g1).clone(), (**p1).clone()));
                        stack.push(MatchTask::MatchName((**g0).clone(), (**p0).clone()));
                    }
                    (Name::MApplyProc(_, _), Name::MApplyProc(_, _)) => return None,
                    (Name::LamName(g0), Name::LamName(p0)) => {
                        let g_inner = g0.inner();
                        let p_inner = p0.inner();
                        let body_match = (*g_inner.unsafe_body)
                            .match_pattern(&*p_inner.unsafe_body);
                        match body_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                    (Name::MLamName(g0), Name::MLamName(p0)) => {
                        let g_inner = g0.inner();
                        let p_inner = p0.inner();
                        if g_inner.unsafe_pattern.len() != p_inner.unsafe_pattern.len() {
                            return None;
                        }
                        let body_match = (*g_inner.unsafe_body)
                            .match_pattern(&*p_inner.unsafe_body);
                        match body_match {
                            Some(b) => bindings.merge(b),
                            None => return None,
                        }
                    }
                    (Name::ApplyName(g0, g1), Name::ApplyName(p0, p1)) => {
                        stack.push(MatchTask::MatchName((**g1).clone(), (**p1).clone()));
                        stack.push(MatchTask::MatchName((**g0).clone(), (**p0).clone()));
                    }
                    (Name::MApplyName(_, _), Name::MApplyName(_, _)) => return None,
                    _ => return None,
                }
            }
        }
    }
    Some(bindings)
}
impl Proc {
    /// First-order pattern matching: match `self` (ground term) against
    /// `pattern` (may contain FreeVars).
    ///
    /// Returns `Some(bindings)` if the match succeeds, `None` otherwise.
    /// Variable patterns bind the entire ground term at that position.
    ///
    /// Uses an iterative work stack for stack safety (supports 100K+
    /// nesting depth). Collection and Binder matching re-enter the
    /// engine via this method, bounded by element/binder count.
    pub fn match_pattern(&self, pattern: &Proc) -> Option<MatchBindings> {
        MATCH_TASK_POOL
            .with(|cell| {
                let mut stack = cell.take();
                stack.clear();
                stack.push(MatchTask::MatchProc(self.clone(), pattern.clone()));
                let result = match_pattern_iterative(&mut stack);
                cell.set(stack);
                result
            })
    }
    /// Alias for uniform cross-category dispatch.
    #[inline]
    pub fn match_pattern_proc(&self, pattern: &Proc) -> Option<MatchBindings> {
        self.match_pattern(pattern)
    }
    /// Cross-category pattern matching (always None — types differ).
    #[inline]
    pub fn match_pattern_name(&self, _pattern: &Name) -> Option<MatchBindings> {
        None
    }
}
impl Name {
    /// First-order pattern matching: match `self` (ground term) against
    /// `pattern` (may contain FreeVars).
    ///
    /// Returns `Some(bindings)` if the match succeeds, `None` otherwise.
    /// Variable patterns bind the entire ground term at that position.
    ///
    /// Uses an iterative work stack for stack safety (supports 100K+
    /// nesting depth). Collection and Binder matching re-enter the
    /// engine via this method, bounded by element/binder count.
    pub fn match_pattern(&self, pattern: &Name) -> Option<MatchBindings> {
        MATCH_TASK_POOL
            .with(|cell| {
                let mut stack = cell.take();
                stack.clear();
                stack.push(MatchTask::MatchName(self.clone(), pattern.clone()));
                let result = match_pattern_iterative(&mut stack);
                cell.set(stack);
                result
            })
    }
    /// Alias for uniform cross-category dispatch.
    #[inline]
    pub fn match_pattern_name(&self, pattern: &Name) -> Option<MatchBindings> {
        self.match_pattern(pattern)
    }
    /// Cross-category pattern matching (always None — types differ).
    #[inline]
    pub fn match_pattern_proc(&self, _pattern: &Proc) -> Option<MatchBindings> {
        None
    }
}
/// Holds a cloned value of any category. Used as the element type in
/// the result buffer for the iterative clone engine.
#[allow(dead_code)]
enum AnyClonedTerm {
    WrapProc(Proc),
    WrapName(Name),
}
/// Work item for the iterative clone engine.
///
/// `Clone{Cat}` variants initiate cloning of a term at a source pointer,
/// storing the result in the given slot.
///
/// `Assemble{Label}` variants reconstruct a parent node from its
/// already-cloned children (referenced by slot indices).
#[allow(dead_code)]
enum CloneTask {
    CloneProc { src: *const Proc, slot: usize },
    CloneName { src: *const Name, slot: usize },
    AssembleProc_PIn { slot: usize, f0_slot: usize, f1_slot: usize },
    AssembleProc_POut { slot: usize, f0_slot: usize, f1_slot: usize },
    AssembleProc_POpen { slot: usize, f0_slot: usize, f1_slot: usize },
    AssembleProc_PAmb { slot: usize, f0_slot: usize, f1_slot: usize },
    AssembleProc_PNew {
        slot: usize,
        cloned_pattern: mettail_runtime::Binder<String>,
        body_slot: usize,
    },
    AssembleProc_PPar {
        slot: usize,
        elements_start: usize,
        elements_count: usize,
        counts_vec: Vec<usize>,
    },
    AssembleProc_LamProc {
        slot: usize,
        cloned_pattern: mettail_runtime::Binder<String>,
        body_slot: usize,
    },
    AssembleProc_MLamProc {
        slot: usize,
        cloned_pattern: Vec<mettail_runtime::Binder<String>>,
        body_slot: usize,
    },
    AssembleProc_ApplyProc { slot: usize, f0_slot: usize, f1_slot: usize },
    AssembleProc_MApplyProc {
        slot: usize,
        f0_slot: usize,
        f1_start: usize,
        f1_count: usize,
    },
    AssembleProc_LamName {
        slot: usize,
        cloned_pattern: mettail_runtime::Binder<String>,
        body_slot: usize,
    },
    AssembleProc_MLamName {
        slot: usize,
        cloned_pattern: Vec<mettail_runtime::Binder<String>>,
        body_slot: usize,
    },
    AssembleProc_ApplyName { slot: usize, f0_slot: usize, f1_slot: usize },
    AssembleProc_MApplyName {
        slot: usize,
        f0_slot: usize,
        f1_start: usize,
        f1_count: usize,
    },
    AssembleName_LamProc {
        slot: usize,
        cloned_pattern: mettail_runtime::Binder<String>,
        body_slot: usize,
    },
    AssembleName_MLamProc {
        slot: usize,
        cloned_pattern: Vec<mettail_runtime::Binder<String>>,
        body_slot: usize,
    },
    AssembleName_ApplyProc { slot: usize, f0_slot: usize, f1_slot: usize },
    AssembleName_MApplyProc {
        slot: usize,
        f0_slot: usize,
        f1_start: usize,
        f1_count: usize,
    },
    AssembleName_LamName {
        slot: usize,
        cloned_pattern: mettail_runtime::Binder<String>,
        body_slot: usize,
    },
    AssembleName_MLamName {
        slot: usize,
        cloned_pattern: Vec<mettail_runtime::Binder<String>>,
        body_slot: usize,
    },
    AssembleName_ApplyName { slot: usize, f0_slot: usize, f1_slot: usize },
    AssembleName_MApplyName {
        slot: usize,
        f0_slot: usize,
        f1_start: usize,
        f1_count: usize,
    },
}
thread_local! {
    #[doc = r" Pool for reusing `CloneTask` work stacks across `clone()` calls."] static
    CLONE_TASK_POOL : std::cell::Cell < Vec < CloneTask >> =
    std::cell::Cell::new(Vec::new()); #[doc =
    r" Pool for reusing result buffers across `clone()` calls."] static CLONE_RESULT_POOL
    : std::cell::Cell < Vec < Option < AnyClonedTerm >> > =
    std::cell::Cell::new(Vec::new());
}
/// Iterative clone engine. Processes the work stack until empty.
///
/// # Safety
///
/// All `*const Cat` pointers in `CloneTask::Clone{Cat}` must be valid
/// for reads for the duration of this function call. This is guaranteed
/// because they are derived from `&self` in `Clone::clone()` and the
/// source tree is immutable (shared reference).
#[allow(dead_code, unused_variables)]
fn clone_iterative(
    stack: &mut Vec<CloneTask>,
    results: &mut Vec<Option<AnyClonedTerm>>,
) {
    while let Some(task) = stack.pop() {
        match task {
            CloneTask::CloneProc { src, slot } => {
                let src_ref = unsafe { &*src };
                match src_ref {
                    Proc::PZero => {
                        results[slot] = Some(AnyClonedTerm::WrapProc(Proc::PZero));
                    }
                    Proc::PIn(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_slot = results.len();
                        results.push(None);
                        stack
                            .push(CloneTask::AssembleProc_PIn {
                                slot,
                                f0_slot,
                                f1_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &**f1 as *const _,
                                slot: f1_slot,
                            });
                    }
                    Proc::POut(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_slot = results.len();
                        results.push(None);
                        stack
                            .push(CloneTask::AssembleProc_POut {
                                slot,
                                f0_slot,
                                f1_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &**f1 as *const _,
                                slot: f1_slot,
                            });
                    }
                    Proc::POpen(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_slot = results.len();
                        results.push(None);
                        stack
                            .push(CloneTask::AssembleProc_POpen {
                                slot,
                                f0_slot,
                                f1_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &**f1 as *const _,
                                slot: f1_slot,
                            });
                    }
                    Proc::PAmb(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_slot = results.len();
                        results.push(None);
                        stack
                            .push(CloneTask::AssembleProc_PAmb {
                                slot,
                                f0_slot,
                                f1_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &**f1 as *const _,
                                slot: f1_slot,
                            });
                    }
                    Proc::PNew(ref f0) => {
                        let body_slot = results.len();
                        results.push(None);
                        let cloned_pattern = f0.inner().unsafe_pattern.clone();
                        stack
                            .push(CloneTask::AssembleProc_PNew {
                                slot,
                                cloned_pattern,
                                body_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &*f0.inner().unsafe_body as *const _,
                                slot: body_slot,
                            });
                    }
                    Proc::PPar(ref coll) => {
                        let elements_start = results.len();
                        let mut counts_vec: Vec<usize> = Vec::new();
                        for (_elem, count) in coll.iter() {
                            results.push(None);
                            counts_vec.push(count);
                        }
                        let elements_count = results.len() - elements_start;
                        stack
                            .push(CloneTask::AssembleProc_PPar {
                                slot,
                                elements_start,
                                elements_count,
                                counts_vec,
                            });
                        for (elem_idx, (elem, _count)) in coll.iter().enumerate() {
                            stack
                                .push(CloneTask::CloneProc {
                                    src: elem as *const _,
                                    slot: elements_start + elem_idx,
                                });
                        }
                    }
                    Proc::PVar(v) => {
                        results[slot] = Some(
                            AnyClonedTerm::WrapProc(Proc::PVar(v.clone())),
                        );
                    }
                    Proc::LamProc(ref f0) => {
                        let body_slot = results.len();
                        results.push(None);
                        let cloned_pattern = f0.inner().unsafe_pattern.clone();
                        stack
                            .push(CloneTask::AssembleProc_LamProc {
                                slot,
                                cloned_pattern,
                                body_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &*f0.inner().unsafe_body as *const _,
                                slot: body_slot,
                            });
                    }
                    Proc::MLamProc(ref f0) => {
                        let body_slot = results.len();
                        results.push(None);
                        let cloned_pattern = f0.inner().unsafe_pattern.clone();
                        stack
                            .push(CloneTask::AssembleProc_MLamProc {
                                slot,
                                cloned_pattern,
                                body_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &*f0.inner().unsafe_body as *const _,
                                slot: body_slot,
                            });
                    }
                    Proc::ApplyProc(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_slot = results.len();
                        results.push(None);
                        stack
                            .push(CloneTask::AssembleProc_ApplyProc {
                                slot,
                                f0_slot,
                                f1_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &**f1 as *const _,
                                slot: f1_slot,
                            });
                    }
                    Proc::MApplyProc(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_start = results.len();
                        for _ in 0..f1.len() {
                            results.push(None);
                        }
                        let f1_count = f1.len();
                        stack
                            .push(CloneTask::AssembleProc_MApplyProc {
                                slot,
                                f0_slot,
                                f1_start,
                                f1_count,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        for (idx, elem) in f1.iter().enumerate().rev() {
                            stack
                                .push(CloneTask::CloneProc {
                                    src: elem as *const _,
                                    slot: f1_start + idx,
                                });
                        }
                    }
                    Proc::LamName(ref f0) => {
                        let body_slot = results.len();
                        results.push(None);
                        let cloned_pattern = f0.inner().unsafe_pattern.clone();
                        stack
                            .push(CloneTask::AssembleProc_LamName {
                                slot,
                                cloned_pattern,
                                body_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &*f0.inner().unsafe_body as *const _,
                                slot: body_slot,
                            });
                    }
                    Proc::MLamName(ref f0) => {
                        let body_slot = results.len();
                        results.push(None);
                        let cloned_pattern = f0.inner().unsafe_pattern.clone();
                        stack
                            .push(CloneTask::AssembleProc_MLamName {
                                slot,
                                cloned_pattern,
                                body_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &*f0.inner().unsafe_body as *const _,
                                slot: body_slot,
                            });
                    }
                    Proc::ApplyName(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_slot = results.len();
                        results.push(None);
                        stack
                            .push(CloneTask::AssembleProc_ApplyName {
                                slot,
                                f0_slot,
                                f1_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &**f1 as *const _,
                                slot: f1_slot,
                            });
                    }
                    Proc::MApplyName(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_start = results.len();
                        for _ in 0..f1.len() {
                            results.push(None);
                        }
                        let f1_count = f1.len();
                        stack
                            .push(CloneTask::AssembleProc_MApplyName {
                                slot,
                                f0_slot,
                                f1_start,
                                f1_count,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        for (idx, elem) in f1.iter().enumerate().rev() {
                            stack
                                .push(CloneTask::CloneName {
                                    src: elem as *const _,
                                    slot: f1_start + idx,
                                });
                        }
                    }
                }
            }
            CloneTask::CloneName { src, slot } => {
                let src_ref = unsafe { &*src };
                match src_ref {
                    Name::NVar(v) => {
                        results[slot] = Some(
                            AnyClonedTerm::WrapName(Name::NVar(v.clone())),
                        );
                    }
                    Name::LamProc(ref f0) => {
                        let body_slot = results.len();
                        results.push(None);
                        let cloned_pattern = f0.inner().unsafe_pattern.clone();
                        stack
                            .push(CloneTask::AssembleName_LamProc {
                                slot,
                                cloned_pattern,
                                body_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &*f0.inner().unsafe_body as *const _,
                                slot: body_slot,
                            });
                    }
                    Name::MLamProc(ref f0) => {
                        let body_slot = results.len();
                        results.push(None);
                        let cloned_pattern = f0.inner().unsafe_pattern.clone();
                        stack
                            .push(CloneTask::AssembleName_MLamProc {
                                slot,
                                cloned_pattern,
                                body_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &*f0.inner().unsafe_body as *const _,
                                slot: body_slot,
                            });
                    }
                    Name::ApplyProc(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_slot = results.len();
                        results.push(None);
                        stack
                            .push(CloneTask::AssembleName_ApplyProc {
                                slot,
                                f0_slot,
                                f1_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        stack
                            .push(CloneTask::CloneProc {
                                src: &**f1 as *const _,
                                slot: f1_slot,
                            });
                    }
                    Name::MApplyProc(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_start = results.len();
                        for _ in 0..f1.len() {
                            results.push(None);
                        }
                        let f1_count = f1.len();
                        stack
                            .push(CloneTask::AssembleName_MApplyProc {
                                slot,
                                f0_slot,
                                f1_start,
                                f1_count,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        for (idx, elem) in f1.iter().enumerate().rev() {
                            stack
                                .push(CloneTask::CloneProc {
                                    src: elem as *const _,
                                    slot: f1_start + idx,
                                });
                        }
                    }
                    Name::LamName(ref f0) => {
                        let body_slot = results.len();
                        results.push(None);
                        let cloned_pattern = f0.inner().unsafe_pattern.clone();
                        stack
                            .push(CloneTask::AssembleName_LamName {
                                slot,
                                cloned_pattern,
                                body_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &*f0.inner().unsafe_body as *const _,
                                slot: body_slot,
                            });
                    }
                    Name::MLamName(ref f0) => {
                        let body_slot = results.len();
                        results.push(None);
                        let cloned_pattern = f0.inner().unsafe_pattern.clone();
                        stack
                            .push(CloneTask::AssembleName_MLamName {
                                slot,
                                cloned_pattern,
                                body_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &*f0.inner().unsafe_body as *const _,
                                slot: body_slot,
                            });
                    }
                    Name::ApplyName(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_slot = results.len();
                        results.push(None);
                        stack
                            .push(CloneTask::AssembleName_ApplyName {
                                slot,
                                f0_slot,
                                f1_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &**f1 as *const _,
                                slot: f1_slot,
                            });
                    }
                    Name::MApplyName(ref f0, ref f1) => {
                        let f0_slot = results.len();
                        results.push(None);
                        let f1_start = results.len();
                        for _ in 0..f1.len() {
                            results.push(None);
                        }
                        let f1_count = f1.len();
                        stack
                            .push(CloneTask::AssembleName_MApplyName {
                                slot,
                                f0_slot,
                                f1_start,
                                f1_count,
                            });
                        stack
                            .push(CloneTask::CloneName {
                                src: &**f0 as *const _,
                                slot: f0_slot,
                            });
                        for (idx, elem) in f1.iter().enumerate().rev() {
                            stack
                                .push(CloneTask::CloneName {
                                    src: elem as *const _,
                                    slot: f1_start + idx,
                                });
                        }
                    }
                }
            }
            CloneTask::AssembleProc_PIn { slot, f0_slot, f1_slot } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let field_1 = match results[f1_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                results[slot] = Some(
                    AnyClonedTerm::WrapProc(
                        Proc::PIn(Box::new(field_0), Box::new(field_1)),
                    ),
                );
            }
            CloneTask::AssembleProc_POut { slot, f0_slot, f1_slot } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let field_1 = match results[f1_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                results[slot] = Some(
                    AnyClonedTerm::WrapProc(
                        Proc::POut(Box::new(field_0), Box::new(field_1)),
                    ),
                );
            }
            CloneTask::AssembleProc_POpen { slot, f0_slot, f1_slot } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let field_1 = match results[f1_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                results[slot] = Some(
                    AnyClonedTerm::WrapProc(
                        Proc::POpen(Box::new(field_0), Box::new(field_1)),
                    ),
                );
            }
            CloneTask::AssembleProc_PAmb { slot, f0_slot, f1_slot } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let field_1 = match results[f1_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                results[slot] = Some(
                    AnyClonedTerm::WrapProc(
                        Proc::PAmb(Box::new(field_0), Box::new(field_1)),
                    ),
                );
            }
            CloneTask::AssembleProc_PNew { slot, cloned_pattern, body_slot } => {
                let body = match results[body_slot]
                    .take()
                    .expect("iterative clone: missing binder body")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => {
                        unreachable!(
                            "iterative clone: wrong category in binder body slot"
                        )
                    }
                };
                let new_scope = mettail_runtime::Scope::from_parts_unsafe(
                    cloned_pattern,
                    Box::new(body),
                );
                results[slot] = Some(AnyClonedTerm::WrapProc(Proc::PNew(new_scope)));
            }
            CloneTask::AssembleProc_PPar {
                slot,
                elements_start,
                elements_count,
                counts_vec,
            } => {
                let mut bag = mettail_runtime::HashBag::new();
                for (idx, count) in counts_vec.iter().enumerate() {
                    match results[elements_start + idx]
                        .take()
                        .expect("iterative clone: missing hashbag element")
                    {
                        AnyClonedTerm::WrapProc(v) => bag.insert_n(v, *count),
                        _ => {
                            unreachable!(
                                "iterative clone: wrong category in hashbag slot"
                            )
                        }
                    }
                }
                results[slot] = Some(AnyClonedTerm::WrapProc(Proc::PPar(bag)));
            }
            CloneTask::AssembleProc_LamProc { slot, cloned_pattern, body_slot } => {
                let body = match results[body_slot]
                    .take()
                    .expect("iterative clone: missing binder body")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => {
                        unreachable!(
                            "iterative clone: wrong category in binder body slot"
                        )
                    }
                };
                let new_scope = mettail_runtime::Scope::from_parts_unsafe(
                    cloned_pattern,
                    Box::new(body),
                );
                results[slot] = Some(AnyClonedTerm::WrapProc(Proc::LamProc(new_scope)));
            }
            CloneTask::AssembleProc_MLamProc { slot, cloned_pattern, body_slot } => {
                let body = match results[body_slot]
                    .take()
                    .expect("iterative clone: missing multi-binder body")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => {
                        unreachable!(
                            "iterative clone: wrong category in multi-binder body slot"
                        )
                    }
                };
                let new_scope = mettail_runtime::Scope::from_parts_unsafe(
                    cloned_pattern,
                    Box::new(body),
                );
                results[slot] = Some(AnyClonedTerm::WrapProc(Proc::MLamProc(new_scope)));
            }
            CloneTask::AssembleProc_ApplyProc { slot, f0_slot, f1_slot } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let field_1 = match results[f1_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                results[slot] = Some(
                    AnyClonedTerm::WrapProc(
                        Proc::ApplyProc(Box::new(field_0), Box::new(field_1)),
                    ),
                );
            }
            CloneTask::AssembleProc_MApplyProc { slot, f0_slot, f1_start, f1_count } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let mut field_1 = Vec::with_capacity(f1_count);
                for idx in 0..f1_count {
                    match results[f1_start + idx]
                        .take()
                        .expect("iterative clone: missing collection element")
                    {
                        AnyClonedTerm::WrapProc(v) => field_1.push(v),
                        _ => {
                            unreachable!(
                                "iterative clone: wrong category in collection slot"
                            )
                        }
                    }
                }
                results[slot] = Some(
                    AnyClonedTerm::WrapProc(Proc::MApplyProc(Box::new(field_0), field_1)),
                );
            }
            CloneTask::AssembleProc_LamName { slot, cloned_pattern, body_slot } => {
                let body = match results[body_slot]
                    .take()
                    .expect("iterative clone: missing binder body")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => {
                        unreachable!(
                            "iterative clone: wrong category in binder body slot"
                        )
                    }
                };
                let new_scope = mettail_runtime::Scope::from_parts_unsafe(
                    cloned_pattern,
                    Box::new(body),
                );
                results[slot] = Some(AnyClonedTerm::WrapProc(Proc::LamName(new_scope)));
            }
            CloneTask::AssembleProc_MLamName { slot, cloned_pattern, body_slot } => {
                let body = match results[body_slot]
                    .take()
                    .expect("iterative clone: missing multi-binder body")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => {
                        unreachable!(
                            "iterative clone: wrong category in multi-binder body slot"
                        )
                    }
                };
                let new_scope = mettail_runtime::Scope::from_parts_unsafe(
                    cloned_pattern,
                    Box::new(body),
                );
                results[slot] = Some(AnyClonedTerm::WrapProc(Proc::MLamName(new_scope)));
            }
            CloneTask::AssembleProc_ApplyName { slot, f0_slot, f1_slot } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let field_1 = match results[f1_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                results[slot] = Some(
                    AnyClonedTerm::WrapProc(
                        Proc::ApplyName(Box::new(field_0), Box::new(field_1)),
                    ),
                );
            }
            CloneTask::AssembleProc_MApplyName { slot, f0_slot, f1_start, f1_count } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let mut field_1 = Vec::with_capacity(f1_count);
                for idx in 0..f1_count {
                    match results[f1_start + idx]
                        .take()
                        .expect("iterative clone: missing collection element")
                    {
                        AnyClonedTerm::WrapName(v) => field_1.push(v),
                        _ => {
                            unreachable!(
                                "iterative clone: wrong category in collection slot"
                            )
                        }
                    }
                }
                results[slot] = Some(
                    AnyClonedTerm::WrapProc(Proc::MApplyName(Box::new(field_0), field_1)),
                );
            }
            CloneTask::AssembleName_LamProc { slot, cloned_pattern, body_slot } => {
                let body = match results[body_slot]
                    .take()
                    .expect("iterative clone: missing binder body")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => {
                        unreachable!(
                            "iterative clone: wrong category in binder body slot"
                        )
                    }
                };
                let new_scope = mettail_runtime::Scope::from_parts_unsafe(
                    cloned_pattern,
                    Box::new(body),
                );
                results[slot] = Some(AnyClonedTerm::WrapName(Name::LamProc(new_scope)));
            }
            CloneTask::AssembleName_MLamProc { slot, cloned_pattern, body_slot } => {
                let body = match results[body_slot]
                    .take()
                    .expect("iterative clone: missing multi-binder body")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => {
                        unreachable!(
                            "iterative clone: wrong category in multi-binder body slot"
                        )
                    }
                };
                let new_scope = mettail_runtime::Scope::from_parts_unsafe(
                    cloned_pattern,
                    Box::new(body),
                );
                results[slot] = Some(AnyClonedTerm::WrapName(Name::MLamProc(new_scope)));
            }
            CloneTask::AssembleName_ApplyProc { slot, f0_slot, f1_slot } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let field_1 = match results[f1_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapProc(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                results[slot] = Some(
                    AnyClonedTerm::WrapName(
                        Name::ApplyProc(Box::new(field_0), Box::new(field_1)),
                    ),
                );
            }
            CloneTask::AssembleName_MApplyProc { slot, f0_slot, f1_start, f1_count } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let mut field_1 = Vec::with_capacity(f1_count);
                for idx in 0..f1_count {
                    match results[f1_start + idx]
                        .take()
                        .expect("iterative clone: missing collection element")
                    {
                        AnyClonedTerm::WrapProc(v) => field_1.push(v),
                        _ => {
                            unreachable!(
                                "iterative clone: wrong category in collection slot"
                            )
                        }
                    }
                }
                results[slot] = Some(
                    AnyClonedTerm::WrapName(Name::MApplyProc(Box::new(field_0), field_1)),
                );
            }
            CloneTask::AssembleName_LamName { slot, cloned_pattern, body_slot } => {
                let body = match results[body_slot]
                    .take()
                    .expect("iterative clone: missing binder body")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => {
                        unreachable!(
                            "iterative clone: wrong category in binder body slot"
                        )
                    }
                };
                let new_scope = mettail_runtime::Scope::from_parts_unsafe(
                    cloned_pattern,
                    Box::new(body),
                );
                results[slot] = Some(AnyClonedTerm::WrapName(Name::LamName(new_scope)));
            }
            CloneTask::AssembleName_MLamName { slot, cloned_pattern, body_slot } => {
                let body = match results[body_slot]
                    .take()
                    .expect("iterative clone: missing multi-binder body")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => {
                        unreachable!(
                            "iterative clone: wrong category in multi-binder body slot"
                        )
                    }
                };
                let new_scope = mettail_runtime::Scope::from_parts_unsafe(
                    cloned_pattern,
                    Box::new(body),
                );
                results[slot] = Some(AnyClonedTerm::WrapName(Name::MLamName(new_scope)));
            }
            CloneTask::AssembleName_ApplyName { slot, f0_slot, f1_slot } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let field_1 = match results[f1_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                results[slot] = Some(
                    AnyClonedTerm::WrapName(
                        Name::ApplyName(Box::new(field_0), Box::new(field_1)),
                    ),
                );
            }
            CloneTask::AssembleName_MApplyName { slot, f0_slot, f1_start, f1_count } => {
                let field_0 = match results[f0_slot]
                    .take()
                    .expect("iterative clone: missing result in slot")
                {
                    AnyClonedTerm::WrapName(v) => v,
                    _ => unreachable!("iterative clone: wrong category in slot"),
                };
                let mut field_1 = Vec::with_capacity(f1_count);
                for idx in 0..f1_count {
                    match results[f1_start + idx]
                        .take()
                        .expect("iterative clone: missing collection element")
                    {
                        AnyClonedTerm::WrapName(v) => field_1.push(v),
                        _ => {
                            unreachable!(
                                "iterative clone: wrong category in collection slot"
                            )
                        }
                    }
                }
                results[slot] = Some(
                    AnyClonedTerm::WrapName(Name::MApplyName(Box::new(field_0), field_1)),
                );
            }
        }
    }
}
impl Clone for Proc {
    fn clone(&self) -> Self {
        let tls_result = CLONE_TASK_POOL
            .try_with(|task_cell| {
                CLONE_RESULT_POOL
                    .try_with(|result_cell| {
                        let mut stack = task_cell.take();
                        let mut results = result_cell.take();
                        stack.clear();
                        results.clear();
                        results.push(None);
                        stack
                            .push(CloneTask::CloneProc {
                                src: self as *const _,
                                slot: 0,
                            });
                        clone_iterative(&mut stack, &mut results);
                        let root = match results[0]
                            .take()
                            .expect("iterative clone: root slot empty after clone")
                        {
                            AnyClonedTerm::WrapProc(v) => v,
                            _ => {
                                unreachable!("iterative clone: wrong category in root slot")
                            }
                        };
                        result_cell.set(results);
                        task_cell.set(stack);
                        root
                    })
            });
        if let Ok(Ok(root)) = tls_result {
            return root;
        }
        let mut stack = Vec::new();
        let mut results = vec![None];
        stack
            .push(CloneTask::CloneProc {
                src: self as *const _,
                slot: 0,
            });
        clone_iterative(&mut stack, &mut results);
        match results[0]
            .take()
            .expect("iterative clone: root slot empty after clone (fallback)")
        {
            AnyClonedTerm::WrapProc(v) => v,
            _ => unreachable!("iterative clone: wrong category in root slot (fallback)"),
        }
    }
}
impl Clone for Name {
    fn clone(&self) -> Self {
        let tls_result = CLONE_TASK_POOL
            .try_with(|task_cell| {
                CLONE_RESULT_POOL
                    .try_with(|result_cell| {
                        let mut stack = task_cell.take();
                        let mut results = result_cell.take();
                        stack.clear();
                        results.clear();
                        results.push(None);
                        stack
                            .push(CloneTask::CloneName {
                                src: self as *const _,
                                slot: 0,
                            });
                        clone_iterative(&mut stack, &mut results);
                        let root = match results[0]
                            .take()
                            .expect("iterative clone: root slot empty after clone")
                        {
                            AnyClonedTerm::WrapName(v) => v,
                            _ => {
                                unreachable!("iterative clone: wrong category in root slot")
                            }
                        };
                        result_cell.set(results);
                        task_cell.set(stack);
                        root
                    })
            });
        if let Ok(Ok(root)) = tls_result {
            return root;
        }
        let mut stack = Vec::new();
        let mut results = vec![None];
        stack
            .push(CloneTask::CloneName {
                src: self as *const _,
                slot: 0,
            });
        clone_iterative(&mut stack, &mut results);
        match results[0]
            .take()
            .expect("iterative clone: root slot empty after clone (fallback)")
        {
            AnyClonedTerm::WrapName(v) => v,
            _ => unreachable!("iterative clone: wrong category in root slot (fallback)"),
        }
    }
}
/// Work item for the iterative comparison engines (eq and cmp).
///
/// Each variant wraps a pair of raw pointers to values of the same
/// category. The iterative engine pops tasks, compares discriminants
/// and leaf payloads, and pushes child-pair tasks for `Box<T>` fields.
#[allow(dead_code)]
enum CmpTask {
    CmpProc(*const Proc, *const Proc),
    CmpName(*const Name, *const Name),
}
unsafe impl Send for CmpTask {}
unsafe impl Sync for CmpTask {}
thread_local! {
    #[doc = r" Pool for reusing `CmpTask` work stacks across comparison calls."] #[doc =
    r""] #[doc = r" The `Cell<Vec<CmpTask>>` pattern allows zero-allocation"] #[doc =
    r" steady-state operation: the first comparison allocates, subsequent"] #[doc =
    r" comparisons reuse the same buffer. Re-entrant comparisons (from"] #[doc =
    r" collection fields delegating to their own PartialEq/Ord) get fresh"] #[doc =
    r" empty vectors; the outermost call retains pool capacity."] static CMP_TASK_POOL :
    std::cell::Cell < Vec < CmpTask >> = std::cell::Cell::new(Vec::new());
}
/// Map a variant to its declaration-order index for Ord comparison.
#[inline]
#[allow(dead_code)]
fn variant_index_proc(val: &Proc) -> usize {
    match val {
        Proc::PZero => 0usize,
        Proc::PIn(..) => 1usize,
        Proc::POut(..) => 2usize,
        Proc::POpen(..) => 3usize,
        Proc::PAmb(..) => 4usize,
        Proc::PNew(..) => 5usize,
        Proc::PPar(..) => 6usize,
        Proc::PVar(..) => 7usize,
        Proc::LamProc(..) => 8usize,
        Proc::MLamProc(..) => 9usize,
        Proc::ApplyProc(..) => 10usize,
        Proc::MApplyProc(..) => 11usize,
        Proc::LamName(..) => 12usize,
        Proc::MLamName(..) => 13usize,
        Proc::ApplyName(..) => 14usize,
        Proc::MApplyName(..) => 15usize,
    }
}
/// Map a variant to its declaration-order index for Ord comparison.
#[inline]
#[allow(dead_code)]
fn variant_index_name(val: &Name) -> usize {
    match val {
        Name::NVar(..) => 0usize,
        Name::LamProc(..) => 1usize,
        Name::MLamProc(..) => 2usize,
        Name::ApplyProc(..) => 3usize,
        Name::MApplyProc(..) => 4usize,
        Name::LamName(..) => 5usize,
        Name::MLamName(..) => 6usize,
        Name::ApplyName(..) => 7usize,
        Name::MApplyName(..) => 8usize,
    }
}
/// Iterative equality engine. Processes the work stack until empty.
///
/// Returns `true` if all pushed comparison pairs are equal.
///
/// # Safety
///
/// All `*const Cat` pointers in `CmpTask` must be valid for reads
/// for the duration of this function call. This is guaranteed because
/// they are derived from `&self` and `&other` in `PartialEq::eq()`.
#[allow(dead_code, unused_variables)]
fn eq_iterative(stack: &mut Vec<CmpTask>) -> bool {
    while let Some(task) = stack.pop() {
        match task {
            CmpTask::CmpProc(left_ptr, right_ptr) => {
                let left = unsafe { &*left_ptr };
                let right = unsafe { &*right_ptr };
                if variant_index_proc(left) != variant_index_proc(right) {
                    return false;
                }
                match (left, right) {
                    (Proc::PZero, Proc::PZero) => {}
                    (Proc::PIn(ref l0, ref l1), Proc::PIn(ref r0, ref r1)) => {
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                    }
                    (Proc::POut(ref l0, ref l1), Proc::POut(ref r0, ref r1)) => {
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                    }
                    (Proc::POpen(ref l0, ref l1), Proc::POpen(ref r0, ref r1)) => {
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                    }
                    (Proc::PAmb(ref l0, ref l1), Proc::PAmb(ref r0, ref r1)) => {
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                    }
                    (Proc::PNew(ref l0), Proc::PNew(ref r0)) => {
                        let l_pat = &l0.inner().unsafe_pattern;
                        let r_pat = &r0.inner().unsafe_pattern;
                        if l_pat != r_pat {
                            return false;
                        }
                        let l_body: *const Proc = &*l0.inner().unsafe_body;
                        let r_body: *const Proc = &*r0.inner().unsafe_body;
                        stack.push(CmpTask::CmpProc(l_body, r_body));
                    }
                    (Proc::PPar(a), Proc::PPar(b)) => {
                        if a != b {
                            return false;
                        }
                    }
                    (Proc::PVar(a), Proc::PVar(b)) => {
                        if a != b {
                            return false;
                        }
                    }
                    (Proc::LamProc(ref l0), Proc::LamProc(ref r0)) => {
                        let l_pat = &l0.inner().unsafe_pattern;
                        let r_pat = &r0.inner().unsafe_pattern;
                        if l_pat != r_pat {
                            return false;
                        }
                        let l_body: *const Proc = &*l0.inner().unsafe_body;
                        let r_body: *const Proc = &*r0.inner().unsafe_body;
                        stack.push(CmpTask::CmpProc(l_body, r_body));
                    }
                    (Proc::MLamProc(ref l0), Proc::MLamProc(ref r0)) => {
                        let l_pat = &l0.inner().unsafe_pattern;
                        let r_pat = &r0.inner().unsafe_pattern;
                        if l_pat != r_pat {
                            return false;
                        }
                        let l_body: *const Proc = &*l0.inner().unsafe_body;
                        let r_body: *const Proc = &*r0.inner().unsafe_body;
                        stack.push(CmpTask::CmpProc(l_body, r_body));
                    }
                    (
                        Proc::ApplyProc(ref l0, ref l1),
                        Proc::ApplyProc(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpProc(&**l0 as *const _, &**r0 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                    }
                    (
                        Proc::MApplyProc(ref l0, ref l1),
                        Proc::MApplyProc(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpProc(&**l0 as *const _, &**r0 as *const _),
                            );
                        if l1 != r1 {
                            return false;
                        }
                    }
                    (Proc::LamName(ref l0), Proc::LamName(ref r0)) => {
                        let l_pat = &l0.inner().unsafe_pattern;
                        let r_pat = &r0.inner().unsafe_pattern;
                        if l_pat != r_pat {
                            return false;
                        }
                        let l_body: *const Proc = &*l0.inner().unsafe_body;
                        let r_body: *const Proc = &*r0.inner().unsafe_body;
                        stack.push(CmpTask::CmpProc(l_body, r_body));
                    }
                    (Proc::MLamName(ref l0), Proc::MLamName(ref r0)) => {
                        let l_pat = &l0.inner().unsafe_pattern;
                        let r_pat = &r0.inner().unsafe_pattern;
                        if l_pat != r_pat {
                            return false;
                        }
                        let l_body: *const Proc = &*l0.inner().unsafe_body;
                        let r_body: *const Proc = &*r0.inner().unsafe_body;
                        stack.push(CmpTask::CmpProc(l_body, r_body));
                    }
                    (
                        Proc::ApplyName(ref l0, ref l1),
                        Proc::ApplyName(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpProc(&**l0 as *const _, &**r0 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpName(&**l1 as *const _, &**r1 as *const _),
                            );
                    }
                    (
                        Proc::MApplyName(ref l0, ref l1),
                        Proc::MApplyName(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpProc(&**l0 as *const _, &**r0 as *const _),
                            );
                        if l1 != r1 {
                            return false;
                        }
                    }
                    _ => {
                        return false;
                    }
                }
            }
            CmpTask::CmpName(left_ptr, right_ptr) => {
                let left = unsafe { &*left_ptr };
                let right = unsafe { &*right_ptr };
                if variant_index_name(left) != variant_index_name(right) {
                    return false;
                }
                match (left, right) {
                    (Name::NVar(a), Name::NVar(b)) => {
                        if a != b {
                            return false;
                        }
                    }
                    (Name::LamProc(ref l0), Name::LamProc(ref r0)) => {
                        let l_pat = &l0.inner().unsafe_pattern;
                        let r_pat = &r0.inner().unsafe_pattern;
                        if l_pat != r_pat {
                            return false;
                        }
                        let l_body: *const Name = &*l0.inner().unsafe_body;
                        let r_body: *const Name = &*r0.inner().unsafe_body;
                        stack.push(CmpTask::CmpName(l_body, r_body));
                    }
                    (Name::MLamProc(ref l0), Name::MLamProc(ref r0)) => {
                        let l_pat = &l0.inner().unsafe_pattern;
                        let r_pat = &r0.inner().unsafe_pattern;
                        if l_pat != r_pat {
                            return false;
                        }
                        let l_body: *const Name = &*l0.inner().unsafe_body;
                        let r_body: *const Name = &*r0.inner().unsafe_body;
                        stack.push(CmpTask::CmpName(l_body, r_body));
                    }
                    (
                        Name::ApplyProc(ref l0, ref l1),
                        Name::ApplyProc(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                    }
                    (
                        Name::MApplyProc(ref l0, ref l1),
                        Name::MApplyProc(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                        if l1 != r1 {
                            return false;
                        }
                    }
                    (Name::LamName(ref l0), Name::LamName(ref r0)) => {
                        let l_pat = &l0.inner().unsafe_pattern;
                        let r_pat = &r0.inner().unsafe_pattern;
                        if l_pat != r_pat {
                            return false;
                        }
                        let l_body: *const Name = &*l0.inner().unsafe_body;
                        let r_body: *const Name = &*r0.inner().unsafe_body;
                        stack.push(CmpTask::CmpName(l_body, r_body));
                    }
                    (Name::MLamName(ref l0), Name::MLamName(ref r0)) => {
                        let l_pat = &l0.inner().unsafe_pattern;
                        let r_pat = &r0.inner().unsafe_pattern;
                        if l_pat != r_pat {
                            return false;
                        }
                        let l_body: *const Name = &*l0.inner().unsafe_body;
                        let r_body: *const Name = &*r0.inner().unsafe_body;
                        stack.push(CmpTask::CmpName(l_body, r_body));
                    }
                    (
                        Name::ApplyName(ref l0, ref l1),
                        Name::ApplyName(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpName(&**l1 as *const _, &**r1 as *const _),
                            );
                    }
                    (
                        Name::MApplyName(ref l0, ref l1),
                        Name::MApplyName(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                        if l1 != r1 {
                            return false;
                        }
                    }
                    _ => {
                        return false;
                    }
                }
            }
        }
    }
    true
}
/// Iterative ordering engine. Processes the work stack until empty.
///
/// Returns `std::cmp::Ordering` for the overall comparison.
///
/// # Safety
///
/// All `*const Cat` pointers in `CmpTask` must be valid for reads
/// for the duration of this function call. This is guaranteed because
/// they are derived from `&self` and `&other` in `Ord::cmp()`.
#[allow(dead_code, unused_variables)]
fn cmp_iterative(stack: &mut Vec<CmpTask>) -> std::cmp::Ordering {
    while let Some(task) = stack.pop() {
        match task {
            CmpTask::CmpProc(left_ptr, right_ptr) => {
                let left = unsafe { &*left_ptr };
                let right = unsafe { &*right_ptr };
                let l_idx = variant_index_proc(left);
                let r_idx = variant_index_proc(right);
                if l_idx != r_idx {
                    stack.clear();
                    return l_idx.cmp(&r_idx);
                }
                match (left, right) {
                    (Proc::PZero, Proc::PZero) => {}
                    (Proc::PIn(ref l0, ref l1), Proc::PIn(ref r0, ref r1)) => {
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                    }
                    (Proc::POut(ref l0, ref l1), Proc::POut(ref r0, ref r1)) => {
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                    }
                    (Proc::POpen(ref l0, ref l1), Proc::POpen(ref r0, ref r1)) => {
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                    }
                    (Proc::PAmb(ref l0, ref l1), Proc::PAmb(ref r0, ref r1)) => {
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                    }
                    (Proc::PNew(ref l0), Proc::PNew(ref r0)) => {
                        let l_scope = l0.inner();
                        let r_scope = r0.inner();
                        let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                            let mut h = std::collections::hash_map::DefaultHasher::new();
                            std::hash::Hasher::finish(&h)
                        };
                        let pat_ord = hash_pat(&l_scope.unsafe_pattern)
                            .cmp(&hash_pat(&r_scope.unsafe_pattern));
                        if pat_ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return pat_ord;
                        }
                        let l_body: *const Proc = &*l_scope.unsafe_body;
                        let r_body: *const Proc = &*r_scope.unsafe_body;
                        stack.push(CmpTask::CmpProc(l_body, r_body));
                    }
                    (Proc::PPar(a), Proc::PPar(b)) => {
                        let ord = a.cmp(b);
                        if ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return ord;
                        }
                    }
                    (Proc::PVar(a), Proc::PVar(b)) => {
                        let ord = a.cmp(b);
                        if ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return ord;
                        }
                    }
                    (Proc::LamProc(ref l0), Proc::LamProc(ref r0)) => {
                        let l_scope = l0.inner();
                        let r_scope = r0.inner();
                        let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                            let mut h = std::collections::hash_map::DefaultHasher::new();
                            std::hash::Hasher::finish(&h)
                        };
                        let pat_ord = hash_pat(&l_scope.unsafe_pattern)
                            .cmp(&hash_pat(&r_scope.unsafe_pattern));
                        if pat_ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return pat_ord;
                        }
                        let l_body: *const Proc = &*l_scope.unsafe_body;
                        let r_body: *const Proc = &*r_scope.unsafe_body;
                        stack.push(CmpTask::CmpProc(l_body, r_body));
                    }
                    (Proc::MLamProc(ref l0), Proc::MLamProc(ref r0)) => {
                        let l_scope = l0.inner();
                        let r_scope = r0.inner();
                        let l_pats = &l_scope.unsafe_pattern;
                        let r_pats = &r_scope.unsafe_pattern;
                        let len_ord = l_pats.len().cmp(&r_pats.len());
                        if len_ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return len_ord;
                        }
                        for (lp, rp) in l_pats.iter().zip(r_pats.iter()) {
                            let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                                let mut h = std::collections::hash_map::DefaultHasher::new();
                                std::hash::Hasher::finish(&h)
                            };
                            let pat_ord = hash_pat(lp).cmp(&hash_pat(rp));
                            if pat_ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return pat_ord;
                            }
                        }
                        let l_body: *const Proc = &*l_scope.unsafe_body;
                        let r_body: *const Proc = &*r_scope.unsafe_body;
                        stack.push(CmpTask::CmpProc(l_body, r_body));
                    }
                    (
                        Proc::ApplyProc(ref l0, ref l1),
                        Proc::ApplyProc(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpProc(&**l0 as *const _, &**r0 as *const _),
                            );
                    }
                    (
                        Proc::MApplyProc(ref l0, ref l1),
                        Proc::MApplyProc(ref r0, ref r1),
                    ) => {
                        {
                            let ord = (**l0).cmp(&**r0);
                            if ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return ord;
                            }
                        }
                        {
                            let ord = l1.cmp(r1);
                            if ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return ord;
                            }
                        }
                    }
                    (Proc::LamName(ref l0), Proc::LamName(ref r0)) => {
                        let l_scope = l0.inner();
                        let r_scope = r0.inner();
                        let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                            let mut h = std::collections::hash_map::DefaultHasher::new();
                            std::hash::Hasher::finish(&h)
                        };
                        let pat_ord = hash_pat(&l_scope.unsafe_pattern)
                            .cmp(&hash_pat(&r_scope.unsafe_pattern));
                        if pat_ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return pat_ord;
                        }
                        let l_body: *const Proc = &*l_scope.unsafe_body;
                        let r_body: *const Proc = &*r_scope.unsafe_body;
                        stack.push(CmpTask::CmpProc(l_body, r_body));
                    }
                    (Proc::MLamName(ref l0), Proc::MLamName(ref r0)) => {
                        let l_scope = l0.inner();
                        let r_scope = r0.inner();
                        let l_pats = &l_scope.unsafe_pattern;
                        let r_pats = &r_scope.unsafe_pattern;
                        let len_ord = l_pats.len().cmp(&r_pats.len());
                        if len_ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return len_ord;
                        }
                        for (lp, rp) in l_pats.iter().zip(r_pats.iter()) {
                            let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                                let mut h = std::collections::hash_map::DefaultHasher::new();
                                std::hash::Hasher::finish(&h)
                            };
                            let pat_ord = hash_pat(lp).cmp(&hash_pat(rp));
                            if pat_ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return pat_ord;
                            }
                        }
                        let l_body: *const Proc = &*l_scope.unsafe_body;
                        let r_body: *const Proc = &*r_scope.unsafe_body;
                        stack.push(CmpTask::CmpProc(l_body, r_body));
                    }
                    (
                        Proc::ApplyName(ref l0, ref l1),
                        Proc::ApplyName(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpName(&**l1 as *const _, &**r1 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpProc(&**l0 as *const _, &**r0 as *const _),
                            );
                    }
                    (
                        Proc::MApplyName(ref l0, ref l1),
                        Proc::MApplyName(ref r0, ref r1),
                    ) => {
                        {
                            let ord = (**l0).cmp(&**r0);
                            if ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return ord;
                            }
                        }
                        {
                            let ord = l1.cmp(r1);
                            if ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return ord;
                            }
                        }
                    }
                    _ => {
                        stack.clear();
                        return l_idx.cmp(&r_idx);
                    }
                }
            }
            CmpTask::CmpName(left_ptr, right_ptr) => {
                let left = unsafe { &*left_ptr };
                let right = unsafe { &*right_ptr };
                let l_idx = variant_index_name(left);
                let r_idx = variant_index_name(right);
                if l_idx != r_idx {
                    stack.clear();
                    return l_idx.cmp(&r_idx);
                }
                match (left, right) {
                    (Name::NVar(a), Name::NVar(b)) => {
                        let ord = a.cmp(b);
                        if ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return ord;
                        }
                    }
                    (Name::LamProc(ref l0), Name::LamProc(ref r0)) => {
                        let l_scope = l0.inner();
                        let r_scope = r0.inner();
                        let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                            let mut h = std::collections::hash_map::DefaultHasher::new();
                            std::hash::Hasher::finish(&h)
                        };
                        let pat_ord = hash_pat(&l_scope.unsafe_pattern)
                            .cmp(&hash_pat(&r_scope.unsafe_pattern));
                        if pat_ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return pat_ord;
                        }
                        let l_body: *const Name = &*l_scope.unsafe_body;
                        let r_body: *const Name = &*r_scope.unsafe_body;
                        stack.push(CmpTask::CmpName(l_body, r_body));
                    }
                    (Name::MLamProc(ref l0), Name::MLamProc(ref r0)) => {
                        let l_scope = l0.inner();
                        let r_scope = r0.inner();
                        let l_pats = &l_scope.unsafe_pattern;
                        let r_pats = &r_scope.unsafe_pattern;
                        let len_ord = l_pats.len().cmp(&r_pats.len());
                        if len_ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return len_ord;
                        }
                        for (lp, rp) in l_pats.iter().zip(r_pats.iter()) {
                            let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                                let mut h = std::collections::hash_map::DefaultHasher::new();
                                std::hash::Hasher::finish(&h)
                            };
                            let pat_ord = hash_pat(lp).cmp(&hash_pat(rp));
                            if pat_ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return pat_ord;
                            }
                        }
                        let l_body: *const Name = &*l_scope.unsafe_body;
                        let r_body: *const Name = &*r_scope.unsafe_body;
                        stack.push(CmpTask::CmpName(l_body, r_body));
                    }
                    (
                        Name::ApplyProc(ref l0, ref l1),
                        Name::ApplyProc(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpProc(&**l1 as *const _, &**r1 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                    }
                    (
                        Name::MApplyProc(ref l0, ref l1),
                        Name::MApplyProc(ref r0, ref r1),
                    ) => {
                        {
                            let ord = (**l0).cmp(&**r0);
                            if ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return ord;
                            }
                        }
                        {
                            let ord = l1.cmp(r1);
                            if ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return ord;
                            }
                        }
                    }
                    (Name::LamName(ref l0), Name::LamName(ref r0)) => {
                        let l_scope = l0.inner();
                        let r_scope = r0.inner();
                        let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                            let mut h = std::collections::hash_map::DefaultHasher::new();
                            std::hash::Hasher::finish(&h)
                        };
                        let pat_ord = hash_pat(&l_scope.unsafe_pattern)
                            .cmp(&hash_pat(&r_scope.unsafe_pattern));
                        if pat_ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return pat_ord;
                        }
                        let l_body: *const Name = &*l_scope.unsafe_body;
                        let r_body: *const Name = &*r_scope.unsafe_body;
                        stack.push(CmpTask::CmpName(l_body, r_body));
                    }
                    (Name::MLamName(ref l0), Name::MLamName(ref r0)) => {
                        let l_scope = l0.inner();
                        let r_scope = r0.inner();
                        let l_pats = &l_scope.unsafe_pattern;
                        let r_pats = &r_scope.unsafe_pattern;
                        let len_ord = l_pats.len().cmp(&r_pats.len());
                        if len_ord != std::cmp::Ordering::Equal {
                            stack.clear();
                            return len_ord;
                        }
                        for (lp, rp) in l_pats.iter().zip(r_pats.iter()) {
                            let hash_pat = |p: &mettail_runtime::Binder<String>| -> u64 {
                                let mut h = std::collections::hash_map::DefaultHasher::new();
                                std::hash::Hasher::finish(&h)
                            };
                            let pat_ord = hash_pat(lp).cmp(&hash_pat(rp));
                            if pat_ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return pat_ord;
                            }
                        }
                        let l_body: *const Name = &*l_scope.unsafe_body;
                        let r_body: *const Name = &*r_scope.unsafe_body;
                        stack.push(CmpTask::CmpName(l_body, r_body));
                    }
                    (
                        Name::ApplyName(ref l0, ref l1),
                        Name::ApplyName(ref r0, ref r1),
                    ) => {
                        stack
                            .push(
                                CmpTask::CmpName(&**l1 as *const _, &**r1 as *const _),
                            );
                        stack
                            .push(
                                CmpTask::CmpName(&**l0 as *const _, &**r0 as *const _),
                            );
                    }
                    (
                        Name::MApplyName(ref l0, ref l1),
                        Name::MApplyName(ref r0, ref r1),
                    ) => {
                        {
                            let ord = (**l0).cmp(&**r0);
                            if ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return ord;
                            }
                        }
                        {
                            let ord = l1.cmp(r1);
                            if ord != std::cmp::Ordering::Equal {
                                stack.clear();
                                return ord;
                            }
                        }
                    }
                    _ => {
                        stack.clear();
                        return l_idx.cmp(&r_idx);
                    }
                }
            }
        }
    }
    std::cmp::Ordering::Equal
}
impl PartialEq for Proc {
    fn eq(&self, other: &Self) -> bool {
        let tls_result = CMP_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                let was_empty = stack.is_empty();
                stack.push(CmpTask::CmpProc(self as *const _, other as *const _));
                let result = eq_iterative(&mut stack);
                if was_empty {
                    stack.clear();
                }
                cell.set(stack);
                result
            });
        if let Ok(result) = tls_result {
            return result;
        }
        let mut stack = vec![CmpTask::CmpProc(self as * const _, other as * const _,)];
        eq_iterative(&mut stack)
    }
}
impl Eq for Proc {}
impl PartialOrd for Proc {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Proc {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let tls_result = CMP_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                let was_empty = stack.is_empty();
                stack.push(CmpTask::CmpProc(self as *const _, other as *const _));
                let result = cmp_iterative(&mut stack);
                if was_empty {
                    stack.clear();
                }
                cell.set(stack);
                result
            });
        if let Ok(result) = tls_result {
            return result;
        }
        let mut stack = vec![CmpTask::CmpProc(self as * const _, other as * const _,)];
        cmp_iterative(&mut stack)
    }
}
impl PartialEq for Name {
    fn eq(&self, other: &Self) -> bool {
        let tls_result = CMP_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                let was_empty = stack.is_empty();
                stack.push(CmpTask::CmpName(self as *const _, other as *const _));
                let result = eq_iterative(&mut stack);
                if was_empty {
                    stack.clear();
                }
                cell.set(stack);
                result
            });
        if let Ok(result) = tls_result {
            return result;
        }
        let mut stack = vec![CmpTask::CmpName(self as * const _, other as * const _,)];
        eq_iterative(&mut stack)
    }
}
impl Eq for Name {}
impl PartialOrd for Name {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Name {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let tls_result = CMP_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                let was_empty = stack.is_empty();
                stack.push(CmpTask::CmpName(self as *const _, other as *const _));
                let result = cmp_iterative(&mut stack);
                if was_empty {
                    stack.clear();
                }
                cell.set(stack);
                result
            });
        if let Ok(result) = tls_result {
            return result;
        }
        let mut stack = vec![CmpTask::CmpName(self as * const _, other as * const _,)];
        cmp_iterative(&mut stack)
    }
}
/// Work item for the iterative drop engine.
///
/// Each variant wraps an owned value of one category. The iterative
/// engine pops tasks, extracts their children (replacing with dummies),
/// pushes children as new tasks, and lets the (now dummy-filled) value
/// be dropped cheaply by the compiler.
#[allow(dead_code)]
enum DropTask {
    DropProc(Proc),
    DropName(Name),
}
thread_local! {
    #[doc = r" Pool for reusing `DropTask` work stacks across `drop()` calls."] #[doc =
    r""] #[doc = r" The `Cell<Vec<DropTask>>` pattern allows zero-allocation"] #[doc =
    r" steady-state operation: the first drop allocates, subsequent"] #[doc =
    r" drops reuse the same buffer. Re-entrant drops (from inner"] #[doc =
    r" values being dropped during processing) get fresh empty vectors;"] #[doc =
    r" the outermost call retains pool capacity."] static DROP_TASK_POOL :
    std::cell::Cell < Vec < DropTask >> = std::cell::Cell::new(Vec::new()); #[doc =
    r" Flag indicating the current thread is inside the iterative"] #[doc =
    r" drop loop. When set, inner `Drop::drop` calls skip the"] #[doc =
    r" iterative logic — the value being dropped has already had its"] #[doc =
    r" children extracted (replaced with dummies), so the compiler's"] #[doc =
    r" default field-by-field drop is safe and O(1)."] static DROP_ACTIVE :
    std::cell::Cell < bool > = std::cell::Cell::new(false);
}
/// Return the cheapest possible leaf value for this category.
///
/// Used as a placeholder when extracting children during
/// iterative drop. Must be a leaf (no `Box<T>` children).
#[inline]
#[allow(dead_code)]
fn dummy_proc() -> Proc {
    Proc::PZero
}
#[inline]
#[allow(dead_code)]
fn dummy_name() -> Name {
    Name::NVar(
        mettail_runtime::OrdVar(
            mettail_runtime::Var::Free(mettail_runtime::FreeVar::fresh(None)),
        ),
    )
}
/// Extract `Box<T>` children from a category value, replacing them
/// with dummy values, and push the extracted children as `DropTask`s
/// onto the work stack.
#[allow(dead_code, unused_variables)]
fn push_drop_children_proc(value: &mut Proc, stack: &mut Vec<DropTask>) {
    match value {
        Proc::PZero => {}
        Proc::PIn(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_name()));
            stack.push(DropTask::DropName(*child));
            let child = std::mem::replace(f1, Box::new(dummy_proc()));
            stack.push(DropTask::DropProc(*child));
        }
        Proc::POut(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_name()));
            stack.push(DropTask::DropName(*child));
            let child = std::mem::replace(f1, Box::new(dummy_proc()));
            stack.push(DropTask::DropProc(*child));
        }
        Proc::POpen(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_name()));
            stack.push(DropTask::DropName(*child));
            let child = std::mem::replace(f1, Box::new(dummy_proc()));
            stack.push(DropTask::DropProc(*child));
        }
        Proc::PAmb(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_name()));
            stack.push(DropTask::DropName(*child));
            let child = std::mem::replace(f1, Box::new(dummy_proc()));
            stack.push(DropTask::DropProc(*child));
        }
        Proc::PNew(ref mut f0) => {
            let dummy_scope = mettail_runtime::Scope::from_parts_unsafe(
                mettail_runtime::Binder(mettail_runtime::FreeVar::fresh(None)),
                Box::new(dummy_proc()),
            );
            let old_scope = std::mem::replace(f0, dummy_scope);
            let (_pattern, body) = old_scope.into_parts_unsafe();
            stack.push(DropTask::DropProc(*body));
        }
        Proc::PPar(ref mut coll) => {
            for (elem, _count) in std::mem::take(coll).into_iter() {
                stack.push(DropTask::DropProc(elem));
            }
        }
        Proc::PVar(_) => {}
        Proc::LamProc(ref mut f0) => {
            let dummy_scope = mettail_runtime::Scope::from_parts_unsafe(
                mettail_runtime::Binder(mettail_runtime::FreeVar::fresh(None)),
                Box::new(dummy_proc()),
            );
            let old_scope = std::mem::replace(f0, dummy_scope);
            let (_pattern, body) = old_scope.into_parts_unsafe();
            stack.push(DropTask::DropProc(*body));
        }
        Proc::MLamProc(ref mut f0) => {
            let dummy_scope = mettail_runtime::Scope::from_parts_unsafe(
                Vec::new(),
                Box::new(dummy_proc()),
            );
            let old_scope = std::mem::replace(f0, dummy_scope);
            let (_pattern, body) = old_scope.into_parts_unsafe();
            stack.push(DropTask::DropProc(*body));
        }
        Proc::ApplyProc(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_proc()));
            stack.push(DropTask::DropProc(*child));
            let child = std::mem::replace(f1, Box::new(dummy_proc()));
            stack.push(DropTask::DropProc(*child));
        }
        Proc::MApplyProc(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_proc()));
            stack.push(DropTask::DropProc(*child));
            for elem in std::mem::take(f1) {
                stack.push(DropTask::DropProc(elem));
            }
        }
        Proc::LamName(ref mut f0) => {
            let dummy_scope = mettail_runtime::Scope::from_parts_unsafe(
                mettail_runtime::Binder(mettail_runtime::FreeVar::fresh(None)),
                Box::new(dummy_proc()),
            );
            let old_scope = std::mem::replace(f0, dummy_scope);
            let (_pattern, body) = old_scope.into_parts_unsafe();
            stack.push(DropTask::DropProc(*body));
        }
        Proc::MLamName(ref mut f0) => {
            let dummy_scope = mettail_runtime::Scope::from_parts_unsafe(
                Vec::new(),
                Box::new(dummy_proc()),
            );
            let old_scope = std::mem::replace(f0, dummy_scope);
            let (_pattern, body) = old_scope.into_parts_unsafe();
            stack.push(DropTask::DropProc(*body));
        }
        Proc::ApplyName(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_proc()));
            stack.push(DropTask::DropProc(*child));
            let child = std::mem::replace(f1, Box::new(dummy_name()));
            stack.push(DropTask::DropName(*child));
        }
        Proc::MApplyName(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_proc()));
            stack.push(DropTask::DropProc(*child));
            for elem in std::mem::take(f1) {
                stack.push(DropTask::DropName(elem));
            }
        }
    }
}
/// Extract `Box<T>` children from a category value, replacing them
/// with dummy values, and push the extracted children as `DropTask`s
/// onto the work stack.
#[allow(dead_code, unused_variables)]
fn push_drop_children_name(value: &mut Name, stack: &mut Vec<DropTask>) {
    match value {
        Name::NVar(_) => {}
        Name::LamProc(ref mut f0) => {
            let dummy_scope = mettail_runtime::Scope::from_parts_unsafe(
                mettail_runtime::Binder(mettail_runtime::FreeVar::fresh(None)),
                Box::new(dummy_name()),
            );
            let old_scope = std::mem::replace(f0, dummy_scope);
            let (_pattern, body) = old_scope.into_parts_unsafe();
            stack.push(DropTask::DropName(*body));
        }
        Name::MLamProc(ref mut f0) => {
            let dummy_scope = mettail_runtime::Scope::from_parts_unsafe(
                Vec::new(),
                Box::new(dummy_name()),
            );
            let old_scope = std::mem::replace(f0, dummy_scope);
            let (_pattern, body) = old_scope.into_parts_unsafe();
            stack.push(DropTask::DropName(*body));
        }
        Name::ApplyProc(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_name()));
            stack.push(DropTask::DropName(*child));
            let child = std::mem::replace(f1, Box::new(dummy_proc()));
            stack.push(DropTask::DropProc(*child));
        }
        Name::MApplyProc(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_name()));
            stack.push(DropTask::DropName(*child));
            for elem in std::mem::take(f1) {
                stack.push(DropTask::DropProc(elem));
            }
        }
        Name::LamName(ref mut f0) => {
            let dummy_scope = mettail_runtime::Scope::from_parts_unsafe(
                mettail_runtime::Binder(mettail_runtime::FreeVar::fresh(None)),
                Box::new(dummy_name()),
            );
            let old_scope = std::mem::replace(f0, dummy_scope);
            let (_pattern, body) = old_scope.into_parts_unsafe();
            stack.push(DropTask::DropName(*body));
        }
        Name::MLamName(ref mut f0) => {
            let dummy_scope = mettail_runtime::Scope::from_parts_unsafe(
                Vec::new(),
                Box::new(dummy_name()),
            );
            let old_scope = std::mem::replace(f0, dummy_scope);
            let (_pattern, body) = old_scope.into_parts_unsafe();
            stack.push(DropTask::DropName(*body));
        }
        Name::ApplyName(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_name()));
            stack.push(DropTask::DropName(*child));
            let child = std::mem::replace(f1, Box::new(dummy_name()));
            stack.push(DropTask::DropName(*child));
        }
        Name::MApplyName(ref mut f0, ref mut f1) => {
            let child = std::mem::replace(f0, Box::new(dummy_name()));
            stack.push(DropTask::DropName(*child));
            for elem in std::mem::take(f1) {
                stack.push(DropTask::DropName(elem));
            }
        }
    }
}
impl Drop for Proc {
    fn drop(&mut self) {
        let skip = DROP_ACTIVE.try_with(|flag| flag.get()).unwrap_or(false);
        if skip {
            return;
        }
        let tls_available = DROP_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                let is_outermost = stack.is_empty();
                push_drop_children_proc(self, &mut stack);
                if is_outermost {
                    let _ = DROP_ACTIVE.try_with(|flag| flag.set(true));
                    while let Some(task) = stack.pop() {
                        match task {
                            DropTask::DropProc(mut val) => {
                                push_drop_children_proc(&mut val, &mut stack);
                            }
                            DropTask::DropName(mut val) => {
                                push_drop_children_name(&mut val, &mut stack);
                            }
                        }
                    }
                    let _ = DROP_ACTIVE.try_with(|flag| flag.set(false));
                    cell.set(stack);
                } else {
                    cell.set(stack);
                }
            });
        if tls_available.is_err() {
            let mut stack = Vec::new();
            push_drop_children_proc(self, &mut stack);
            while let Some(task) = stack.pop() {
                match task {
                    DropTask::DropProc(mut val) => {
                        push_drop_children_proc(&mut val, &mut stack);
                    }
                    DropTask::DropName(mut val) => {
                        push_drop_children_name(&mut val, &mut stack);
                    }
                }
            }
        }
    }
}
impl Drop for Name {
    fn drop(&mut self) {
        let skip = DROP_ACTIVE.try_with(|flag| flag.get()).unwrap_or(false);
        if skip {
            return;
        }
        let tls_available = DROP_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                let is_outermost = stack.is_empty();
                push_drop_children_name(self, &mut stack);
                if is_outermost {
                    let _ = DROP_ACTIVE.try_with(|flag| flag.set(true));
                    while let Some(task) = stack.pop() {
                        match task {
                            DropTask::DropProc(mut val) => {
                                push_drop_children_proc(&mut val, &mut stack);
                            }
                            DropTask::DropName(mut val) => {
                                push_drop_children_name(&mut val, &mut stack);
                            }
                        }
                    }
                    let _ = DROP_ACTIVE.try_with(|flag| flag.set(false));
                    cell.set(stack);
                } else {
                    cell.set(stack);
                }
            });
        if tls_available.is_err() {
            let mut stack = Vec::new();
            push_drop_children_name(self, &mut stack);
            while let Some(task) = stack.pop() {
                match task {
                    DropTask::DropProc(mut val) => {
                        push_drop_children_proc(&mut val, &mut stack);
                    }
                    DropTask::DropName(mut val) => {
                        push_drop_children_name(&mut val, &mut stack);
                    }
                }
            }
        }
    }
}
/// Work item for the iterative hash engine.
///
/// Each variant wraps a raw pointer to a value of one category.
/// The iterative engine pops tasks, hashes discriminant and leaf
/// payloads, and pushes child tasks for `Box<T>` fields.
#[allow(dead_code)]
enum HashTask {
    HashProc(*const Proc),
    HashName(*const Name),
}
unsafe impl Send for HashTask {}
unsafe impl Sync for HashTask {}
thread_local! {
    #[doc = r" Pool for reusing `HashTask` work stacks across `hash()` calls."] #[doc =
    r""] #[doc = r" The `Cell<Vec<HashTask>>` pattern allows zero-allocation"] #[doc =
    r" steady-state operation: the first hash allocates, subsequent"] #[doc =
    r" hashes reuse the same buffer. Re-entrant hashes (from"] #[doc =
    r" collection fields delegating to their own Hash) get fresh"] #[doc =
    r" empty vectors; the outermost call retains pool capacity."] static HASH_TASK_POOL :
    std::cell::Cell < Vec < HashTask >> = std::cell::Cell::new(Vec::new());
}
/// Iterative hash engine. Processes the work stack until empty,
/// hashing each node's fields into the provided `Hasher` state.
///
/// # Safety
///
/// All `*const Cat` pointers in `HashTask` must be valid for reads
/// for the duration of this function call. This is guaranteed because
/// they are derived from `&self` in `Hash::hash()`.
#[allow(dead_code, unused_variables)]
fn hash_iterative<H: std::hash::Hasher>(stack: &mut Vec<HashTask>, state: &mut H) {
    while let Some(task) = stack.pop() {
        match task {
            HashTask::HashProc(ptr) => {
                let val = unsafe { &*ptr };
                std::hash::Hash::hash(&variant_index_proc(val), state);
                match val {
                    Proc::PZero => {}
                    Proc::PIn(ref f0, ref f1) => {
                        stack.push(HashTask::HashProc(&**f1 as *const _));
                        stack.push(HashTask::HashName(&**f0 as *const _));
                    }
                    Proc::POut(ref f0, ref f1) => {
                        stack.push(HashTask::HashProc(&**f1 as *const _));
                        stack.push(HashTask::HashName(&**f0 as *const _));
                    }
                    Proc::POpen(ref f0, ref f1) => {
                        stack.push(HashTask::HashProc(&**f1 as *const _));
                        stack.push(HashTask::HashName(&**f0 as *const _));
                    }
                    Proc::PAmb(ref f0, ref f1) => {
                        stack.push(HashTask::HashProc(&**f1 as *const _));
                        stack.push(HashTask::HashName(&**f0 as *const _));
                    }
                    Proc::PNew(ref f0) => {
                        std::hash::Hash::hash(&f0.inner().unsafe_pattern, state);
                        let body_ptr: *const Proc = &*f0.inner().unsafe_body;
                        stack.push(HashTask::HashProc(body_ptr));
                    }
                    Proc::PPar(coll) => {
                        std::hash::Hash::hash(coll, state);
                    }
                    Proc::PVar(v) => {
                        std::hash::Hash::hash(v, state);
                    }
                    Proc::LamProc(ref f0) => {
                        std::hash::Hash::hash(&f0.inner().unsafe_pattern, state);
                        let body_ptr: *const Proc = &*f0.inner().unsafe_body;
                        stack.push(HashTask::HashProc(body_ptr));
                    }
                    Proc::MLamProc(ref f0) => {
                        std::hash::Hash::hash(&f0.inner().unsafe_pattern, state);
                        let body_ptr: *const Proc = &*f0.inner().unsafe_body;
                        stack.push(HashTask::HashProc(body_ptr));
                    }
                    Proc::ApplyProc(ref f0, ref f1) => {
                        stack.push(HashTask::HashProc(&**f1 as *const _));
                        stack.push(HashTask::HashProc(&**f0 as *const _));
                    }
                    Proc::MApplyProc(ref f0, ref f1) => {
                        std::hash::Hash::hash(&**f0, state);
                        std::hash::Hash::hash(f1, state);
                    }
                    Proc::LamName(ref f0) => {
                        std::hash::Hash::hash(&f0.inner().unsafe_pattern, state);
                        let body_ptr: *const Proc = &*f0.inner().unsafe_body;
                        stack.push(HashTask::HashProc(body_ptr));
                    }
                    Proc::MLamName(ref f0) => {
                        std::hash::Hash::hash(&f0.inner().unsafe_pattern, state);
                        let body_ptr: *const Proc = &*f0.inner().unsafe_body;
                        stack.push(HashTask::HashProc(body_ptr));
                    }
                    Proc::ApplyName(ref f0, ref f1) => {
                        stack.push(HashTask::HashName(&**f1 as *const _));
                        stack.push(HashTask::HashProc(&**f0 as *const _));
                    }
                    Proc::MApplyName(ref f0, ref f1) => {
                        std::hash::Hash::hash(&**f0, state);
                        std::hash::Hash::hash(f1, state);
                    }
                }
            }
            HashTask::HashName(ptr) => {
                let val = unsafe { &*ptr };
                std::hash::Hash::hash(&variant_index_name(val), state);
                match val {
                    Name::NVar(v) => {
                        std::hash::Hash::hash(v, state);
                    }
                    Name::LamProc(ref f0) => {
                        std::hash::Hash::hash(&f0.inner().unsafe_pattern, state);
                        let body_ptr: *const Name = &*f0.inner().unsafe_body;
                        stack.push(HashTask::HashName(body_ptr));
                    }
                    Name::MLamProc(ref f0) => {
                        std::hash::Hash::hash(&f0.inner().unsafe_pattern, state);
                        let body_ptr: *const Name = &*f0.inner().unsafe_body;
                        stack.push(HashTask::HashName(body_ptr));
                    }
                    Name::ApplyProc(ref f0, ref f1) => {
                        stack.push(HashTask::HashProc(&**f1 as *const _));
                        stack.push(HashTask::HashName(&**f0 as *const _));
                    }
                    Name::MApplyProc(ref f0, ref f1) => {
                        std::hash::Hash::hash(&**f0, state);
                        std::hash::Hash::hash(f1, state);
                    }
                    Name::LamName(ref f0) => {
                        std::hash::Hash::hash(&f0.inner().unsafe_pattern, state);
                        let body_ptr: *const Name = &*f0.inner().unsafe_body;
                        stack.push(HashTask::HashName(body_ptr));
                    }
                    Name::MLamName(ref f0) => {
                        std::hash::Hash::hash(&f0.inner().unsafe_pattern, state);
                        let body_ptr: *const Name = &*f0.inner().unsafe_body;
                        stack.push(HashTask::HashName(body_ptr));
                    }
                    Name::ApplyName(ref f0, ref f1) => {
                        stack.push(HashTask::HashName(&**f1 as *const _));
                        stack.push(HashTask::HashName(&**f0 as *const _));
                    }
                    Name::MApplyName(ref f0, ref f1) => {
                        std::hash::Hash::hash(&**f0, state);
                        std::hash::Hash::hash(f1, state);
                    }
                }
            }
        }
    }
}
impl std::hash::Hash for Proc {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let tls_result = HASH_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                let was_empty = stack.is_empty();
                stack.push(HashTask::HashProc(self as *const _));
                hash_iterative(&mut stack, state);
                if was_empty {
                    stack.clear();
                }
                cell.set(stack);
            });
        if tls_result.is_ok() {
            return;
        }
        let mut stack = vec![HashTask::HashProc(self as * const _)];
        hash_iterative(&mut stack, state);
    }
}
impl std::hash::Hash for Name {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let tls_result = HASH_TASK_POOL
            .try_with(|cell| {
                let mut stack = cell.take();
                let was_empty = stack.is_empty();
                stack.push(HashTask::HashName(self as *const _));
                hash_iterative(&mut stack, state);
                if was_empty {
                    stack.clear();
                }
                cell.set(stack);
            });
        if tls_result.is_ok() {
            return;
        }
        let mut stack = vec![HashTask::HashName(self as * const _)];
        hash_iterative(&mut stack, state);
    }
}
/// Result of a T3 bounded guard evaluation.
///
/// - `True`: guard definitely holds
/// - `False`: guard definitely does not hold
/// - `Unknown`: depth limit exceeded before determination
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TriState {
    True,
    False,
    Unknown,
}
impl TriState {
    /// Logical conjunction: And(True, True) = True, And(_, False) = False,
    /// And(Unknown, _) = Unknown
    pub fn and(self, other: TriState) -> TriState {
        match (self, other) {
            (TriState::True, TriState::True) => TriState::True,
            (TriState::False, _) | (_, TriState::False) => TriState::False,
            _ => TriState::Unknown,
        }
    }
    /// Logical disjunction: Or(True, _) = True, Or(False, False) = False,
    /// Or(Unknown, _) = Unknown
    pub fn or(self, other: TriState) -> TriState {
        match (self, other) {
            (TriState::True, _) | (_, TriState::True) => TriState::True,
            (TriState::False, TriState::False) => TriState::False,
            _ => TriState::Unknown,
        }
    }
    /// Logical negation: Not(True) = False, Not(False) = True, Not(Unknown) = Unknown
    pub fn not(self) -> TriState {
        match self {
            TriState::True => TriState::False,
            TriState::False => TriState::True,
            TriState::Unknown => TriState::Unknown,
        }
    }
    /// Convert to bool (Unknown → false, conservative).
    pub fn to_bool_conservative(self) -> bool {
        matches!(self, TriState::True)
    }
}
/// Enum representing possible variable categories for type inference
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarCategory {
    Proc,
    Name,
}
/// Inferred type for a variable, including function types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferredType {
    /// Base category (Name, Proc, etc.)
    Base(VarCategory),
    /// Function type [Domain -> Codomain]
    Arrow(Box<InferredType>, Box<InferredType>),
    /// Multi-argument function type [Domain* -> Codomain]
    MultiArrow(Box<InferredType>, Box<InferredType>),
}
impl InferredType {
    /// Get the base representation type (what category stores this type)
    ///
    /// For function types, returns the codomain's base type since
    /// `[A -> B]` is represented as a `B` value (specifically a `LamA` variant).
    pub fn base_type(&self) -> VarCategory {
        match self {
            InferredType::Base(cat) => *cat,
            InferredType::Arrow(_, codomain) => codomain.base_type(),
            InferredType::MultiArrow(_, codomain) => codomain.base_type(),
        }
    }
}
impl std::fmt::Display for InferredType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InferredType::Base(cat) => write!(f, "{:?}", cat),
            InferredType::Arrow(domain, codomain) => {
                write!(f, "[{} -> {}]", domain, codomain)
            }
            InferredType::MultiArrow(domain, codomain) => {
                write!(f, "[{}* -> {}]", domain, codomain)
            }
        }
    }
}
impl Proc {
    /// Find what category a variable is used as in this term (base type only)
    pub fn infer_var_category(&self, var_name: &str) -> Option<VarCategory> {
        match self {
            Proc::PZero => None,
            Proc::PIn(ref f1, ref f3) => {
                if let Some(cat) = f1.infer_var_category(var_name) {
                    return Some(cat);
                }
                if let Some(cat) = f3.infer_var_category(var_name) {
                    return Some(cat);
                }
                None
            }
            Proc::POut(ref f1, ref f3) => {
                if let Some(cat) = f1.infer_var_category(var_name) {
                    return Some(cat);
                }
                if let Some(cat) = f3.infer_var_category(var_name) {
                    return Some(cat);
                }
                None
            }
            Proc::POpen(ref f1, ref f3) => {
                if let Some(cat) = f1.infer_var_category(var_name) {
                    return Some(cat);
                }
                if let Some(cat) = f3.infer_var_category(var_name) {
                    return Some(cat);
                }
                None
            }
            Proc::PAmb(ref f0, ref f2) => {
                if let Some(cat) = f0.infer_var_category(var_name) {
                    return Some(cat);
                }
                if let Some(cat) = f2.infer_var_category(var_name) {
                    return Some(cat);
                }
                None
            }
            Proc::PNew(ref f0) => {
                if let Some(cat) = f0.unsafe_body().infer_var_category(var_name) {
                    return Some(cat);
                }
                None
            }
            Proc::PPar(ref f0) => {
                for (item, _count) in f0.iter() {
                    if let Some(cat) = item.infer_var_category(var_name) {
                        return Some(cat);
                    }
                }
                None
            }
            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) => {
                if fv.pretty_name.as_deref() == Some(var_name) {
                    return Some(VarCategory::Proc);
                }
                None
            }
            _ => None,
        }
    }
    /// Find the full type of a variable from its usage in this term
    ///
    /// Returns function types when variable is used in application position.
    /// For example, in `$name(f, x)`, `f` has type `[Name -> Proc]`.
    pub fn infer_var_type(&self, var_name: &str) -> Option<InferredType> {
        match self {
            Proc::PZero => None,
            Proc::PIn(ref f1, ref f3) => {
                if let Some(t) = f1.infer_var_type(var_name) {
                    return Some(t);
                }
                if let Some(t) = f3.infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Proc::POut(ref f1, ref f3) => {
                if let Some(t) = f1.infer_var_type(var_name) {
                    return Some(t);
                }
                if let Some(t) = f3.infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Proc::POpen(ref f1, ref f3) => {
                if let Some(t) = f1.infer_var_type(var_name) {
                    return Some(t);
                }
                if let Some(t) = f3.infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Proc::PAmb(ref f0, ref f2) => {
                if let Some(t) = f0.infer_var_type(var_name) {
                    return Some(t);
                }
                if let Some(t) = f2.infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Proc::PNew(ref f0) => {
                if let Some(t) = f0.unsafe_body().infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Proc::PPar(ref f0) => {
                for (item, _count) in f0.iter() {
                    if let Some(t) = item.infer_var_type(var_name) {
                        return Some(t);
                    }
                }
                None
            }
            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) => {
                if fv.pretty_name.as_deref() == Some(var_name) {
                    return Some(InferredType::Base(VarCategory::Proc));
                }
                None
            }
            Proc::ApplyProc(ref lam, ref arg) => {
                if let Proc::PVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)),
                ) = **lam {
                    if fv.pretty_name.as_deref() == Some(var_name) {
                        return Some(
                            InferredType::Arrow(
                                Box::new(InferredType::Base(VarCategory::Proc)),
                                Box::new(InferredType::Base(VarCategory::Proc)),
                            ),
                        );
                    }
                }
                if let Some(t) = lam.infer_var_type(var_name) {
                    return Some(t);
                }
                if let Some(t) = arg.infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Proc::MApplyProc(ref lam, ref args) => {
                if let Proc::PVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)),
                ) = **lam {
                    if fv.pretty_name.as_deref() == Some(var_name) {
                        return Some(
                            InferredType::MultiArrow(
                                Box::new(InferredType::Base(VarCategory::Proc)),
                                Box::new(InferredType::Base(VarCategory::Proc)),
                            ),
                        );
                    }
                }
                if let Some(t) = lam.infer_var_type(var_name) {
                    return Some(t);
                }
                for arg in args.iter() {
                    if let Some(t) = arg.infer_var_type(var_name) {
                        return Some(t);
                    }
                }
                None
            }
            Proc::LamProc(ref scope) => {
                if let Some(t) = scope.unsafe_body().infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Proc::MLamProc(ref scope) => {
                if let Some(t) = scope.unsafe_body().infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Proc::ApplyName(ref lam, ref arg) => {
                if let Proc::PVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)),
                ) = **lam {
                    if fv.pretty_name.as_deref() == Some(var_name) {
                        return Some(
                            InferredType::Arrow(
                                Box::new(InferredType::Base(VarCategory::Name)),
                                Box::new(InferredType::Base(VarCategory::Proc)),
                            ),
                        );
                    }
                }
                if let Some(t) = lam.infer_var_type(var_name) {
                    return Some(t);
                }
                if let Some(t) = arg.infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Proc::MApplyName(ref lam, ref args) => {
                if let Proc::PVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)),
                ) = **lam {
                    if fv.pretty_name.as_deref() == Some(var_name) {
                        return Some(
                            InferredType::MultiArrow(
                                Box::new(InferredType::Base(VarCategory::Name)),
                                Box::new(InferredType::Base(VarCategory::Proc)),
                            ),
                        );
                    }
                }
                if let Some(t) = lam.infer_var_type(var_name) {
                    return Some(t);
                }
                for arg in args.iter() {
                    if let Some(t) = arg.infer_var_type(var_name) {
                        return Some(t);
                    }
                }
                None
            }
            Proc::LamName(ref scope) => {
                if let Some(t) = scope.unsafe_body().infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Proc::MLamName(ref scope) => {
                if let Some(t) = scope.unsafe_body().infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            _ => None,
        }
    }
}
impl Name {
    /// Find what category a variable is used as in this term (base type only)
    pub fn infer_var_category(&self, var_name: &str) -> Option<VarCategory> {
        match self {
            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) => {
                if fv.pretty_name.as_deref() == Some(var_name) {
                    return Some(VarCategory::Name);
                }
                None
            }
            _ => None,
        }
    }
    /// Find the full type of a variable from its usage in this term
    ///
    /// Returns function types when variable is used in application position.
    /// For example, in `$name(f, x)`, `f` has type `[Name -> Proc]`.
    pub fn infer_var_type(&self, var_name: &str) -> Option<InferredType> {
        match self {
            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) => {
                if fv.pretty_name.as_deref() == Some(var_name) {
                    return Some(InferredType::Base(VarCategory::Name));
                }
                None
            }
            Name::ApplyProc(ref lam, ref arg) => {
                if let Name::NVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)),
                ) = **lam {
                    if fv.pretty_name.as_deref() == Some(var_name) {
                        return Some(
                            InferredType::Arrow(
                                Box::new(InferredType::Base(VarCategory::Proc)),
                                Box::new(InferredType::Base(VarCategory::Name)),
                            ),
                        );
                    }
                }
                if let Some(t) = lam.infer_var_type(var_name) {
                    return Some(t);
                }
                if let Some(t) = arg.infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Name::MApplyProc(ref lam, ref args) => {
                if let Name::NVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)),
                ) = **lam {
                    if fv.pretty_name.as_deref() == Some(var_name) {
                        return Some(
                            InferredType::MultiArrow(
                                Box::new(InferredType::Base(VarCategory::Proc)),
                                Box::new(InferredType::Base(VarCategory::Name)),
                            ),
                        );
                    }
                }
                if let Some(t) = lam.infer_var_type(var_name) {
                    return Some(t);
                }
                for arg in args.iter() {
                    if let Some(t) = arg.infer_var_type(var_name) {
                        return Some(t);
                    }
                }
                None
            }
            Name::LamProc(ref scope) => {
                if let Some(t) = scope.unsafe_body().infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Name::MLamProc(ref scope) => {
                if let Some(t) = scope.unsafe_body().infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Name::ApplyName(ref lam, ref arg) => {
                if let Name::NVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)),
                ) = **lam {
                    if fv.pretty_name.as_deref() == Some(var_name) {
                        return Some(
                            InferredType::Arrow(
                                Box::new(InferredType::Base(VarCategory::Name)),
                                Box::new(InferredType::Base(VarCategory::Name)),
                            ),
                        );
                    }
                }
                if let Some(t) = lam.infer_var_type(var_name) {
                    return Some(t);
                }
                if let Some(t) = arg.infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Name::MApplyName(ref lam, ref args) => {
                if let Name::NVar(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)),
                ) = **lam {
                    if fv.pretty_name.as_deref() == Some(var_name) {
                        return Some(
                            InferredType::MultiArrow(
                                Box::new(InferredType::Base(VarCategory::Name)),
                                Box::new(InferredType::Base(VarCategory::Name)),
                            ),
                        );
                    }
                }
                if let Some(t) = lam.infer_var_type(var_name) {
                    return Some(t);
                }
                for arg in args.iter() {
                    if let Some(t) = arg.infer_var_type(var_name) {
                        return Some(t);
                    }
                }
                None
            }
            Name::LamName(ref scope) => {
                if let Some(t) = scope.unsafe_body().infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            Name::MLamName(ref scope) => {
                if let Some(t) = scope.unsafe_body().infer_var_type(var_name) {
                    return Some(t);
                }
                None
            }
            _ => None,
        }
    }
}
#[derive(Debug, Clone, PartialEq)]
pub enum Token<'a> {
    Eof,
    Ident(&'a str),
    DdollarNameLp,
    DdollarProcLp,
    DollarName,
    DollarProc,
    LParen,
    RParen,
    Comma,
    Dot,
    Kw0,
    LBracket,
    RBracket,
    Caret,
    Tok_69_6e_28,
    KwNew,
    Tok_6f_70_65_6e_28,
    Tok_6f_75_74_28,
    LBrace,
    Pipe,
    RBrace,
}
fn format_token_friendly(token: &Token<'_>) -> String {
    match token {
        Token::Eof => "end of input".to_string(),
        Token::Ident(s) => format!("identifier `{}`", s),
        Token::DdollarNameLp => "`$$name(`".to_string(),
        Token::DdollarProcLp => "`$$proc(`".to_string(),
        Token::DollarName => "`$name`".to_string(),
        Token::DollarProc => "`$proc`".to_string(),
        Token::LParen => "`(`".to_string(),
        Token::RParen => "`)`".to_string(),
        Token::Comma => "`,`".to_string(),
        Token::Dot => "`.`".to_string(),
        Token::Kw0 => "`0`".to_string(),
        Token::LBracket => "`[`".to_string(),
        Token::RBracket => "`]`".to_string(),
        Token::Caret => "`^`".to_string(),
        Token::Tok_69_6e_28 => "`in(`".to_string(),
        Token::KwNew => "`new`".to_string(),
        Token::Tok_6f_70_65_6e_28 => "`open(`".to_string(),
        Token::Tok_6f_75_74_28 => "`out(`".to_string(),
        Token::LBrace => "`{`".to_string(),
        Token::Pipe => "`|`".to_string(),
        Token::RBrace => "`}`".to_string(),
    }
}
use std::borrow::Cow;
use mettail_prattail::runtime_types::*;
static CHAR_CLASS: [u8; 256] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 3, 0, 0, 4, 0, 5, 0, 6, 7, 7, 7, 7, 7, 7, 7,
    7, 7, 0, 0, 0, 0, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8, 8, 9, 0, 10, 11, 8, 0, 12, 8, 13, 8, 14, 8, 8, 8, 15, 8, 8, 8, 16,
    17, 18, 19, 8, 20, 8, 21, 22, 8, 23, 8, 8, 8, 24, 25, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
];
const NUM_CLASSES: usize = 27;
static IS_ACCEPTING: [u64; 1] = [0x00006730f0f1fffc];
#[inline(always)]
fn is_accepting_state(state: u32) -> bool {
    (IS_ACCEPTING[(state >> 6) as usize] >> (state & 63)) & 1 != 0
}
static BITMAPS: [u32; 47] = [
    134217598, 655362, 0, 0, 0, 0, 0, 16773568, 0, 0, 0, 16773568, 16773568, 16773568, 0,
    0, 0, 655360, 4096, 1048576, 16773572, 16773568, 16773568, 16773568, 4096, 1048576,
    65536, 262144, 0, 16773568, 16773568, 16773572, 65536, 262144, 16384, 8192, 16773572,
    0, 16384, 8192, 0, 0, 0, 4, 4, 0, 0,
];
static OFFSETS: [u16; 47] = [
    0, 25, 28, 28, 28, 28, 28, 28, 43, 43, 43, 43, 58, 73, 88, 88, 88, 88, 90, 91, 92,
    108, 123, 138, 153, 154, 155, 156, 157, 157, 172, 187, 203, 204, 205, 206, 207, 223,
    223, 224, 225, 225, 225, 225, 226, 227, 227,
];
static TARGETS: [u32; 227] = [
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 7, 7, 7, 11, 7, 12, 13, 7, 7, 7, 7, 7, 14, 15, 16, 17,
    18, 19, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 20, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 21, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
    7, 7, 22, 7, 7, 23, 7, 24, 25, 26, 27, 28, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 29, 7, 7, 7, 7, 7, 30, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 31, 7, 7, 32, 33, 34, 35, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 36, 7, 7, 7, 7, 7, 7, 37, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 38, 39, 40, 41, 42, 7, 7, 7, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 43, 44, 45, 46,
];
#[inline(always)]
fn dfa_next_cold(state: u32, class: u8) -> u32 {
    let bitmap = BITMAPS[state as usize];
    let bit = 1u32 << (class as u32);
    if bitmap & bit == 0 {
        return u32::MAX;
    }
    let index = (bitmap & (bit - 1)).count_ones() as usize;
    TARGETS[OFFSETS[state as usize] as usize + index]
}
#[inline(always)]
fn dfa_next(state: u32, class: u8) -> u32 {
    match state {
        6u32 => u32::MAX,
        15u32 => u32::MAX,
        4u32 => u32::MAX,
        7u32 => {
            match class {
                6u8 => 7u32,
                7u8 => 7u32,
                8u8 => 7u32,
                12u8 => 7u32,
                13u8 => 7u32,
                14u8 => 7u32,
                15u8 => 7u32,
                16u8 => 7u32,
                17u8 => 7u32,
                18u8 => 7u32,
                19u8 => 7u32,
                20u8 => 7u32,
                21u8 => 7u32,
                22u8 => 7u32,
                23u8 => 7u32,
                _ => u32::MAX,
            }
        }
        22u32 => {
            match class {
                6u8 => 7u32,
                7u8 => 7u32,
                8u8 => 7u32,
                12u8 => 7u32,
                13u8 => 7u32,
                14u8 => 30u32,
                15u8 => 7u32,
                16u8 => 7u32,
                17u8 => 7u32,
                18u8 => 7u32,
                19u8 => 7u32,
                20u8 => 7u32,
                21u8 => 7u32,
                22u8 => 7u32,
                23u8 => 7u32,
                _ => u32::MAX,
            }
        }
        3u32 => u32::MAX,
        18u32 => {
            match class {
                12u8 => 26u32,
                _ => u32::MAX,
            }
        }
        17u32 => {
            match class {
                17u8 => 24u32,
                19u8 => 25u32,
                _ => u32::MAX,
            }
        }
        23u32 => {
            match class {
                6u8 => 7u32,
                7u8 => 7u32,
                8u8 => 7u32,
                12u8 => 7u32,
                13u8 => 7u32,
                14u8 => 7u32,
                15u8 => 7u32,
                16u8 => 7u32,
                17u8 => 7u32,
                18u8 => 7u32,
                19u8 => 7u32,
                20u8 => 7u32,
                21u8 => 31u32,
                22u8 => 7u32,
                23u8 => 7u32,
                _ => u32::MAX,
            }
        }
        11u32 => {
            match class {
                6u8 => 7u32,
                7u8 => 7u32,
                8u8 => 7u32,
                12u8 => 7u32,
                13u8 => 7u32,
                14u8 => 7u32,
                15u8 => 7u32,
                16u8 => 7u32,
                17u8 => 20u32,
                18u8 => 7u32,
                19u8 => 7u32,
                20u8 => 7u32,
                21u8 => 7u32,
                22u8 => 7u32,
                23u8 => 7u32,
                _ => u32::MAX,
            }
        }
        9u32 => u32::MAX,
        14u32 => u32::MAX,
        12u32 => {
            match class {
                6u8 => 7u32,
                7u8 => 7u32,
                8u8 => 7u32,
                12u8 => 7u32,
                13u8 => 7u32,
                14u8 => 21u32,
                15u8 => 7u32,
                16u8 => 7u32,
                17u8 => 7u32,
                18u8 => 7u32,
                19u8 => 7u32,
                20u8 => 7u32,
                21u8 => 7u32,
                22u8 => 7u32,
                23u8 => 7u32,
                _ => u32::MAX,
            }
        }
        13u32 => {
            match class {
                6u8 => 7u32,
                7u8 => 7u32,
                8u8 => 7u32,
                12u8 => 7u32,
                13u8 => 7u32,
                14u8 => 7u32,
                15u8 => 7u32,
                16u8 => 7u32,
                17u8 => 7u32,
                18u8 => 7u32,
                19u8 => 22u32,
                20u8 => 7u32,
                21u8 => 7u32,
                22u8 => 23u32,
                23u8 => 7u32,
                _ => u32::MAX,
            }
        }
        16u32 => u32::MAX,
        1u32 => {
            match class {
                1u8 => 17u32,
                17u8 => 18u32,
                19u8 => 19u32,
                _ => u32::MAX,
            }
        }
        0u32 => {
            match class {
                1u8 => 1u32,
                2u8 => 2u32,
                3u8 => 3u32,
                4u8 => 4u32,
                5u8 => 5u32,
                6u8 => 6u32,
                8u8 => 7u32,
                9u8 => 8u32,
                10u8 => 9u32,
                11u8 => 10u32,
                12u8 => 7u32,
                13u8 => 7u32,
                14u8 => 7u32,
                15u8 => 11u32,
                16u8 => 7u32,
                17u8 => 12u32,
                18u8 => 13u32,
                19u8 => 7u32,
                20u8 => 7u32,
                21u8 => 7u32,
                22u8 => 7u32,
                23u8 => 7u32,
                24u8 => 14u32,
                25u8 => 15u32,
                26u8 => 16u32,
                _ => u32::MAX,
            }
        }
        19u32 => {
            match class {
                20u8 => 27u32,
                _ => u32::MAX,
            }
        }
        20u32 => {
            match class {
                2u8 => 28u32,
                6u8 => 7u32,
                7u8 => 7u32,
                8u8 => 7u32,
                12u8 => 7u32,
                13u8 => 7u32,
                14u8 => 7u32,
                15u8 => 7u32,
                16u8 => 7u32,
                17u8 => 7u32,
                18u8 => 7u32,
                19u8 => 7u32,
                20u8 => 7u32,
                21u8 => 7u32,
                22u8 => 7u32,
                23u8 => 7u32,
                _ => u32::MAX,
            }
        }
        21u32 => {
            match class {
                6u8 => 7u32,
                7u8 => 7u32,
                8u8 => 7u32,
                12u8 => 7u32,
                13u8 => 7u32,
                14u8 => 7u32,
                15u8 => 7u32,
                16u8 => 7u32,
                17u8 => 7u32,
                18u8 => 7u32,
                19u8 => 7u32,
                20u8 => 7u32,
                21u8 => 7u32,
                22u8 => 7u32,
                23u8 => 29u32,
                _ => u32::MAX,
            }
        }
        8u32 => u32::MAX,
        2u32 => u32::MAX,
        10u32 => u32::MAX,
        5u32 => u32::MAX,
        _ => dfa_next_cold(state, class),
    }
}
fn accept_token<'a>(state: u32, text: &'a str) -> Option<Token<'a>> {
    match state {
        2u32 => Some(Token::LParen),
        3u32 => Some(Token::RParen),
        4u32 => Some(Token::Comma),
        5u32 => Some(Token::Dot),
        6u32 => Some(Token::Kw0),
        7u32 => Some(Token::Ident(text)),
        8u32 => Some(Token::LBracket),
        9u32 => Some(Token::RBracket),
        10u32 => Some(Token::Caret),
        11u32 => Some(Token::Ident(text)),
        12u32 => Some(Token::Ident(text)),
        13u32 => Some(Token::Ident(text)),
        14u32 => Some(Token::LBrace),
        15u32 => Some(Token::Pipe),
        16u32 => Some(Token::RBrace),
        20u32 => Some(Token::Ident(text)),
        21u32 => Some(Token::Ident(text)),
        22u32 => Some(Token::Ident(text)),
        23u32 => Some(Token::Ident(text)),
        28u32 => Some(Token::Tok_69_6e_28),
        29u32 => Some(Token::KwNew),
        30u32 => Some(Token::Ident(text)),
        31u32 => Some(Token::Ident(text)),
        36u32 => Some(Token::Ident(text)),
        37u32 => Some(Token::Tok_6f_75_74_28),
        40u32 => Some(Token::DollarName),
        41u32 => Some(Token::DollarProc),
        42u32 => Some(Token::Tok_6f_70_65_6e_28),
        45u32 => Some(Token::DdollarNameLp),
        46u32 => Some(Token::DdollarProcLp),
        _ => None,
    }
}
pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range)>, String> {
    lex_with_file_id(input, None)
}
pub fn lex_with_file_id<'a>(
    input: &'a str,
    file_id: Option<u32>,
) -> Result<Vec<(Token<'a>, Range)>, String> {
    let (mut tokens, eof_pos) = mettail_prattail::runtime_types::lex_core(
        input,
        file_id,
        &CHAR_CLASS,
        dfa_next,
        is_accepting_state,
        accept_token,
    )?;
    tokens
        .push((
            Token::Eof,
            Range {
                start: eof_pos,
                end: eof_pos,
                file_id,
            },
        ));
    Ok(tokens)
}
fn accept_weight(state: u32) -> f64 {
    match state {
        2u32 => 0.0_f64,
        3u32 => 0.0_f64,
        4u32 => 0.0_f64,
        5u32 => 0.0_f64,
        6u32 => 0.0_f64,
        7u32 => 9.0_f64,
        8u32 => 0.0_f64,
        9u32 => 0.0_f64,
        10u32 => 0.0_f64,
        11u32 => 9.0_f64,
        12u32 => 9.0_f64,
        13u32 => 9.0_f64,
        14u32 => 0.0_f64,
        15u32 => 0.0_f64,
        16u32 => 0.0_f64,
        20u32 => 9.0_f64,
        21u32 => 9.0_f64,
        22u32 => 9.0_f64,
        23u32 => 9.0_f64,
        28u32 => 0.0_f64,
        29u32 => 0.0_f64,
        30u32 => 9.0_f64,
        31u32 => 9.0_f64,
        36u32 => 9.0_f64,
        37u32 => 0.0_f64,
        40u32 => 0.0_f64,
        41u32 => 0.0_f64,
        42u32 => 0.0_f64,
        45u32 => 0.0_f64,
        46u32 => 0.0_f64,
        _ => f64::INFINITY,
    }
}
pub fn lex_weighted<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range, f64)>, String> {
    lex_weighted_with_file_id(input, None)
}
pub fn lex_weighted_with_file_id<'a>(
    input: &'a str,
    file_id: Option<u32>,
) -> Result<Vec<(Token<'a>, Range, f64)>, String> {
    let (mut tokens, eof_pos) = mettail_prattail::runtime_types::lex_weighted_core(
        input,
        file_id,
        &CHAR_CLASS,
        dfa_next,
        is_accepting_state,
        accept_token,
        accept_weight,
    )?;
    tokens
        .push((
            Token::Eof,
            Range {
                start: eof_pos,
                end: eof_pos,
                file_id,
            },
            0.0_f64,
        ));
    Ok(tokens)
}
fn accept_alternatives<'a>(state: u32, text: &'a str) -> Vec<(Token<'a>, f64)> {
    match state {
        2u32 => vec![(Token::LParen, 0.0_f64)],
        3u32 => vec![(Token::RParen, 0.0_f64)],
        4u32 => vec![(Token::Comma, 0.0_f64)],
        5u32 => vec![(Token::Dot, 0.0_f64)],
        6u32 => vec![(Token::Kw0, 0.0_f64)],
        7u32 => vec![(Token::Ident(text), 9.0_f64)],
        8u32 => vec![(Token::LBracket, 0.0_f64)],
        9u32 => vec![(Token::RBracket, 0.0_f64)],
        10u32 => vec![(Token::Caret, 0.0_f64)],
        11u32 => vec![(Token::Ident(text), 9.0_f64)],
        12u32 => vec![(Token::Ident(text), 9.0_f64)],
        13u32 => vec![(Token::Ident(text), 9.0_f64)],
        14u32 => vec![(Token::LBrace, 0.0_f64)],
        15u32 => vec![(Token::Pipe, 0.0_f64)],
        16u32 => vec![(Token::RBrace, 0.0_f64)],
        20u32 => vec![(Token::Ident(text), 9.0_f64)],
        21u32 => vec![(Token::Ident(text), 9.0_f64)],
        22u32 => vec![(Token::Ident(text), 9.0_f64)],
        23u32 => vec![(Token::Ident(text), 9.0_f64)],
        28u32 => vec![(Token::Tok_69_6e_28, 0.0_f64)],
        29u32 => {
            vec![
                (Token::KwNew, 0.0_f64), (Token::KwNew, 0.0_f64), (Token::Ident(text),
                9.0_f64),
            ]
        }
        30u32 => vec![(Token::Ident(text), 9.0_f64)],
        31u32 => vec![(Token::Ident(text), 9.0_f64)],
        36u32 => vec![(Token::Ident(text), 9.0_f64)],
        37u32 => vec![(Token::Tok_6f_75_74_28, 0.0_f64)],
        40u32 => vec![(Token::DollarName, 0.0_f64)],
        41u32 => vec![(Token::DollarProc, 0.0_f64)],
        42u32 => vec![(Token::Tok_6f_70_65_6e_28, 0.0_f64)],
        45u32 => vec![(Token::DdollarNameLp, 0.0_f64)],
        46u32 => vec![(Token::DdollarProcLp, 0.0_f64)],
        _ => Vec::new(),
    }
}
pub fn lex_lattice<'a>(
    input: &'a str,
) -> Result<(mettail_prattail::lattice::TokenSource<Token<'a>, Range>, Range), String> {
    lex_lattice_with_file_id(input, None)
}
pub fn lex_lattice_with_file_id<'a>(
    input: &'a str,
    file_id: Option<u32>,
) -> Result<(mettail_prattail::lattice::TokenSource<Token<'a>, Range>, Range), String> {
    let (source, eof_pos) = mettail_prattail::runtime_types::lex_lattice_core(
        input,
        file_id,
        &CHAR_CLASS,
        dfa_next,
        is_accepting_state,
        accept_alternatives,
    )?;
    let eof_range = Range {
        start: eof_pos,
        end: eof_pos,
        file_id,
    };
    match source {
        mettail_prattail::lattice::TokenSource::Linear(mut tokens) => {
            tokens.push((Token::Eof, eof_range));
            Ok((mettail_prattail::lattice::TokenSource::Linear(tokens), eof_range))
        }
        lattice => Ok((lattice, eof_range)),
    }
}
static WFST_TRANSITIONS_Name: &[(u16, u32, f64)] = &[
    (5_u16, 1_u32, 2.0_f64),
    (9_u16, 1_u32, 0.0_f64),
];
static WFST_STATE_OFFSETS_Name: &[(usize, usize, bool, f64)] = &[
    (0_usize, 2_usize, false, f64::INFINITY),
    (2_usize, 0_usize, true, 0.0_f64),
];
static WFST_TOKEN_NAMES_Name: &[&str] = &[
    "Caret",
    "DdollarNameLp",
    "DdollarProcLp",
    "DollarName",
    "DollarProc",
    "Ident",
    "Kw0",
    "KwNew",
    "LBrace",
    "LParen",
    "Tok_69_6e_28",
    "Tok_6f_70_65_6e_28",
    "Tok_6f_75_74_28",
];
static WFST_BEAM_WIDTH_Name: Option<f64> = None;
static PREDICTION_Name: std::sync::LazyLock<mettail_prattail::wfst::PredictionWfst> = std::sync::LazyLock::new(||
{
    mettail_prattail::wfst::PredictionWfst::from_flat(
        "Name",
        WFST_STATE_OFFSETS_Name,
        WFST_TRANSITIONS_Name,
        WFST_TOKEN_NAMES_Name,
        WFST_BEAM_WIDTH_Name,
    )
});
static WFST_TRANSITIONS_Proc: &[(u16, u32, f64)] = &[
    (5_u16, 1_u32, 2.0_f64),
    (6_u16, 1_u32, 0.0_f64),
    (7_u16, 1_u32, 0.0_f64),
    (8_u16, 1_u32, 0.0_f64),
    (9_u16, 1_u32, 0.0_f64),
    (10_u16, 1_u32, 0.0_f64),
    (11_u16, 1_u32, 0.0_f64),
    (12_u16, 1_u32, 0.0_f64),
];
static WFST_STATE_OFFSETS_Proc: &[(usize, usize, bool, f64)] = &[
    (0_usize, 8_usize, false, f64::INFINITY),
    (8_usize, 0_usize, true, 0.0_f64),
];
static WFST_TOKEN_NAMES_Proc: &[&str] = &[
    "Caret",
    "DdollarNameLp",
    "DdollarProcLp",
    "DollarName",
    "DollarProc",
    "Ident",
    "Kw0",
    "KwNew",
    "LBrace",
    "LParen",
    "Tok_69_6e_28",
    "Tok_6f_70_65_6e_28",
    "Tok_6f_75_74_28",
];
static WFST_BEAM_WIDTH_Proc: Option<f64> = None;
static PREDICTION_Proc: std::sync::LazyLock<mettail_prattail::wfst::PredictionWfst> = std::sync::LazyLock::new(||
{
    mettail_prattail::wfst::PredictionWfst::from_flat(
        "Proc",
        WFST_STATE_OFFSETS_Proc,
        WFST_TRANSITIONS_Proc,
        WFST_TOKEN_NAMES_Proc,
        WFST_BEAM_WIDTH_Proc,
    )
});
static RECOVERY_SYNC_TOKENS_Proc: &[u16] = &[
    1_u16, 6_u16, 13_u16, 14_u16, 15_u16, 16_u16,
];
static RECOVERY_SYNC_SOURCES_Proc: &[(u16, u8)] = &[
    (1_u16, 1_u8),
    (6_u16, 0_u8),
    (13_u16, 2_u8),
    (14_u16, 1_u8),
    (15_u16, 1_u8),
    (16_u16, 1_u8),
];
static RECOVERY_TOKEN_NAMES_Proc: &[&str] = &[
    "Comma",
    "Eof",
    "Pipe",
    "RBrace",
    "RBracket",
    "RParen",
];
static RECOVERY_SYNC_TOKENS_Name: &[u16] = &[
    1_u16, 6_u16, 11_u16, 14_u16, 15_u16, 16_u16,
];
static RECOVERY_SYNC_SOURCES_Name: &[(u16, u8)] = &[
    (1_u16, 1_u8),
    (6_u16, 0_u8),
    (11_u16, 2_u8),
    (14_u16, 1_u8),
    (15_u16, 1_u8),
    (16_u16, 1_u8),
];
static RECOVERY_TOKEN_NAMES_Name: &[&str] = &[
    "Comma",
    "Eof",
    "LBracket",
    "RBrace",
    "RBracket",
    "RParen",
];
const RECOVERY_BEAM_WIDTH: Option<f64> = Some(3.0_f64);
static SIM_FIRST_SETS: &[(&str, &[u16])] = &[
    (
        "Proc",
        &[
            0_u16, 2_u16, 3_u16, 4_u16, 5_u16, 7_u16, 8_u16, 9_u16, 10_u16, 12_u16,
            18_u16, 19_u16, 20_u16,
        ],
    ),
    ("Name", &[7_u16, 12_u16]),
];
static SIM_FOLLOW_SETS: &[(&str, &[u16])] = &[
    ("Proc", &[6_u16, 13_u16, 14_u16, 15_u16, 16_u16]),
    ("Name", &[1_u16, 11_u16]),
];
static SIM_INFIX_SETS: &[(&str, &[u16])] = &[("Proc", &[]), ("Name", &[])];
static PARSE_SIMULATOR: std::sync::LazyLock<
    mettail_prattail::recovery::ParseSimulator,
> = std::sync::LazyLock::new(|| {
    mettail_prattail::recovery::ParseSimulator::from_flat(
        SIM_FIRST_SETS,
        SIM_FOLLOW_SETS,
        SIM_INFIX_SETS,
        5,
    )
});
fn token_to_id(t: &Token) -> u16 {
    match t {
        Token::Caret => 0_u16,
        Token::Comma => 1_u16,
        Token::DdollarNameLp => 2_u16,
        Token::DdollarProcLp => 3_u16,
        Token::DollarName => 4_u16,
        Token::DollarProc => 5_u16,
        Token::Eof => 6_u16,
        Token::Ident(_) => 7_u16,
        Token::Kw0 => 8_u16,
        Token::KwNew => 9_u16,
        Token::LBrace => 10_u16,
        Token::LBracket => 11_u16,
        Token::LParen => 12_u16,
        Token::Pipe => 13_u16,
        Token::RBrace => 14_u16,
        Token::RBracket => 15_u16,
        Token::RParen => 16_u16,
        Token::Tok_69_6e_28 => 18_u16,
        Token::Tok_6f_70_65_6e_28 => 19_u16,
        Token::Tok_6f_75_74_28 => 20_u16,
        _ => u16::MAX,
    }
}
fn parse_pamb<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
) -> Result<Proc, ParseError> {
    let name = parse_Name(tokens, pos, 0)?;
    expect_token(tokens, pos, |t| matches!(t, Token::LBracket), "[")?;
    let proc = parse_Proc(tokens, pos, 0)?;
    expect_token(tokens, pos, |t| matches!(t, Token::RBracket), "]")?;
    Ok(Proc::PAmb(Box::new(name), Box::new(proc)))
}
fn parse_lambda<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
) -> Result<Proc, ParseError> {
    expect_token(tokens, pos, |t| matches!(t, Token::Caret), "^")?;
    match peek_token(tokens, *pos) {
        Some(Token::LBracket) => {
            *pos += 1;
            let mut binder_names = Vec::new();
            loop {
                let name = expect_ident(tokens, pos)?;
                binder_names.push(name);
                if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::Comma))
                {
                    *pos += 1;
                } else {
                    break;
                }
            }
            expect_token(tokens, pos, |t| matches!(t, Token::RBracket), "]")?;
            expect_token(tokens, pos, |t| matches!(t, Token::Dot), ".")?;
            expect_token(tokens, pos, |t| matches!(t, Token::LBrace), "{")?;
            let body = parse_Proc(tokens, pos, 0)?;
            expect_token(tokens, pos, |t| matches!(t, Token::RBrace), "}")?;
            let inferred = if let Some(name) = binder_names.first() {
                body.infer_var_type(name)
            } else {
                None
            };
            let binders: Vec<mettail_runtime::Binder<String>> = binder_names
                .into_iter()
                .map(|s| mettail_runtime::Binder(mettail_runtime::get_or_create_var(s)))
                .collect();
            let scope = mettail_runtime::Scope::new(binders, Box::new(body));
            Ok(
                match inferred {
                    Some(InferredType::Base(VarCategory::Proc)) => Proc::MLamProc(scope),
                    Some(InferredType::Base(VarCategory::Name)) => Proc::MLamName(scope),
                    _ => Proc::MLamProc(scope),
                },
            )
        }
        Some(Token::Ident(_)) => {
            let binder_name = expect_ident(tokens, pos)?;
            expect_token(tokens, pos, |t| matches!(t, Token::Dot), ".")?;
            expect_token(tokens, pos, |t| matches!(t, Token::LBrace), "{")?;
            let body = parse_Proc(tokens, pos, 0)?;
            expect_token(tokens, pos, |t| matches!(t, Token::RBrace), "}")?;
            let inferred = body.infer_var_type(&binder_name);
            let scope = mettail_runtime::Scope::new(
                mettail_runtime::Binder(mettail_runtime::get_or_create_var(binder_name)),
                Box::new(body),
            );
            Ok(
                match inferred {
                    Some(InferredType::Base(VarCategory::Proc)) => Proc::LamProc(scope),
                    Some(InferredType::Base(VarCategory::Name)) => Proc::LamName(scope),
                    _ => Proc::LamProc(scope),
                },
            )
        }
        _ => {
            Err(ParseError::UnexpectedToken {
                expected: Cow::Borrowed("identifier or '['"),
                found: format_token_friendly(&tokens[*pos].0),
                range: tokens[*pos].1,
                hint: Some(Cow::Borrowed("expected a variable name or binder list")),
            })
        }
    }
}
fn parse_dollar_proc<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
) -> Result<Proc, ParseError> {
    expect_token(tokens, pos, |t| matches!(t, Token::DollarProc), "$proc")?;
    expect_token(tokens, pos, |t| matches!(t, Token::LParen), "(")?;
    let f = parse_Proc(tokens, pos, 0)?;
    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
    let x = parse_Proc(tokens, pos, 0)?;
    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
    Ok(Proc::ApplyProc(Box::new(f), Box::new(x)))
}
fn parse_ddollar_proc<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
) -> Result<Proc, ParseError> {
    expect_token(tokens, pos, |t| matches!(t, Token::DdollarProcLp), "$$proc(")?;
    let f = parse_Proc(tokens, pos, 0)?;
    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
    let mut args: Vec<Proc> = Vec::new();
    loop {
        let arg = parse_Proc(tokens, pos, 0)?;
        args.push(arg);
        if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::Comma)) {
            *pos += 1;
        } else {
            break;
        }
    }
    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
    Ok(Proc::MApplyProc(Box::new(f), args))
}
fn parse_dollar_name<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
) -> Result<Proc, ParseError> {
    expect_token(tokens, pos, |t| matches!(t, Token::DollarName), "$name")?;
    expect_token(tokens, pos, |t| matches!(t, Token::LParen), "(")?;
    let f = parse_Proc(tokens, pos, 0)?;
    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
    let x = parse_Name(tokens, pos, 0)?;
    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
    Ok(Proc::ApplyName(Box::new(f), Box::new(x)))
}
fn parse_ddollar_name<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
) -> Result<Proc, ParseError> {
    expect_token(tokens, pos, |t| matches!(t, Token::DdollarNameLp), "$$name(")?;
    let f = parse_Proc(tokens, pos, 0)?;
    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
    let mut args: Vec<Name> = Vec::new();
    loop {
        let arg = parse_Name(tokens, pos, 0)?;
        args.push(arg);
        if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::Comma)) {
            *pos += 1;
        } else {
            break;
        }
    }
    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
    Ok(Proc::MApplyName(Box::new(f), args))
}
fn expect_token<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    predicate: impl Fn(&Token) -> bool,
    expected: &'static str,
) -> Result<(), ParseError> {
    if *pos >= tokens.len() {
        let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero());
        return Err(ParseError::UnexpectedEof {
            expected: Cow::Borrowed(expected),
            range: eof_range,
            hint: None,
        });
    }
    if predicate(&tokens[*pos].0) {
        *pos += 1;
        Ok(())
    } else {
        Err(ParseError::UnexpectedToken {
            expected: Cow::Borrowed(expected),
            found: format_token_friendly(&tokens[*pos].0),
            range: tokens[*pos].1,
            hint: None,
        })
    }
}
fn expect_ident<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
) -> Result<String, ParseError> {
    if *pos >= tokens.len() {
        let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero());
        return Err(ParseError::UnexpectedEof {
            expected: Cow::Borrowed("identifier"),
            range: eof_range,
            hint: None,
        });
    }
    match &tokens[*pos].0 {
        Token::Ident(name) => {
            let result = name.to_string();
            *pos += 1;
            Ok(result)
        }
        other => {
            Err(ParseError::UnexpectedToken {
                expected: Cow::Borrowed("identifier"),
                found: format_token_friendly(other),
                range: tokens[*pos].1,
                hint: Some(
                    Cow::Borrowed("expected a variable name, not a keyword or operator"),
                ),
            })
        }
    }
}
fn peek_token<'a, 'b>(
    tokens: &'b [(Token<'a>, Range)],
    pos: usize,
) -> Option<&'b Token<'a>> {
    tokens.get(pos).map(|(t, _)| t)
}
fn peek_ahead<'a, 'b>(
    tokens: &'b [(Token<'a>, Range)],
    pos: usize,
    offset: usize,
) -> Option<&'b Token<'a>> {
    tokens.get(pos + offset).map(|(t, _)| t)
}
#[derive(Debug)]
enum Frame_Proc {
    GroupClose { saved_bp: u8 },
    RD_PIn_0 { saved_bp: u8, name: Name },
    RD_POut_0 { saved_bp: u8, name: Name },
    RD_POpen_0 { saved_bp: u8, name: Name },
    RD_PNew_0 { saved_bp: u8, x: String },
    CollectionElem_PPar {
        elements: mettail_runtime::HashBag<Proc>,
        saved_pos: usize,
        saved_bp: u8,
    },
    LambdaBody_Single { binder_name: String, saved_bp: u8 },
    LambdaBody_Multi { binder_names: Vec<String>, saved_bp: u8 },
    DollarF_Proc { saved_bp: u8 },
    DdollarF_Proc { saved_bp: u8 },
    DollarF_Name { saved_bp: u8 },
    DdollarF_Name { saved_bp: u8 },
    GuardEval { saved_bp: u8 },
}
thread_local! {
    static FRAME_POOL_PROC : std::cell::Cell < Vec < Frame_Proc >> =
    std::cell::Cell::new(Vec::with_capacity(1));
}
thread_local! {
    static FRAME_STATE_PROC : std::cell::Cell < (u16, u8) > = std::cell::Cell::new((0,
    9));
}
fn frame_kind_of_Proc(stack: &[Frame_Proc]) -> u8 {
    match stack.last() {
        Some(Frame_Proc::GroupClose { .. }) => 4_u8,
        Some(Frame_Proc::RD_PIn_0 { .. }) => 9_u8,
        Some(Frame_Proc::RD_POut_0 { .. }) => 9_u8,
        Some(Frame_Proc::RD_POpen_0 { .. }) => 9_u8,
        Some(Frame_Proc::RD_PNew_0 { .. }) => 9_u8,
        Some(Frame_Proc::CollectionElem_PPar { .. }) => 3_u8,
        Some(Frame_Proc::LambdaBody_Single { .. }) => 6_u8,
        Some(Frame_Proc::LambdaBody_Multi { .. }) => 6_u8,
        Some(Frame_Proc::DollarF_Proc { .. }) => 7_u8,
        Some(Frame_Proc::DdollarF_Proc { .. }) => 7_u8,
        Some(Frame_Proc::DollarF_Name { .. }) => 7_u8,
        Some(Frame_Proc::DdollarF_Name { .. }) => 7_u8,
        Some(Frame_Proc::GuardEval { .. }) => 9_u8,
        None => 9_u8,
    }
}
thread_local! {
    static NFA_PREFIX_SPILL_PROC : std::cell::Cell < Vec < (Proc, usize, f64) >> =
    std::cell::Cell::new(Vec::new()); static NFA_FORCED_PREFIX_PROC : std::cell::Cell <
    Option < (Proc, usize, f64) >> = std::cell::Cell::new(None); static
    NFA_PRIMARY_WEIGHT_PROC : std::cell::Cell < f64 > = std::cell::Cell::new(0.5); static
    RUNNING_WEIGHT_PROC : std::cell::Cell < f64 > = std::cell::Cell::new(0.0); static
    PARENT_WEIGHT_PROC : std::cell::Cell < f64 > = std::cell::Cell::new(0.0);
}
#[inline]
pub fn running_weight_Proc() -> f64 {
    RUNNING_WEIGHT_PROC.with(|cell| cell.get())
}
fn parse_Proc<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
) -> Result<Proc, ParseError> {
    RUNNING_WEIGHT_PROC
        .with(|cell| {
            let inherited = PARENT_WEIGHT_PROC
                .with(|p| {
                    let v = p.get();
                    p.set(0.0);
                    v
                });
            cell.set(inherited);
        });
    FRAME_POOL_PROC
        .with(|cell| {
            let mut stack = cell.take();
            let needed = tokens.len() / 2;
            if stack.capacity() < needed {
                stack.reserve(needed - stack.len());
            }
            let result = parse_Proc_impl(tokens, pos, min_bp, &mut stack);
            cell.set(stack);
            result
        })
}
#[cold]
#[inline(never)]
fn __cross_cat_dispatch_Proc<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    out: *mut std::mem::MaybeUninit<Proc>,
    cur_bp: u8,
) -> bool {
    let saved = *pos;
    match &tokens[*pos].0 {
        Token::LParen => {
            let __nt_first_saved = *pos;
            match parse_pamb(tokens, pos) {
                Ok(v) => {
                    unsafe {
                        (*out).write(v);
                    }
                    return true;
                }
                Err(_) => {
                    *pos = __nt_first_saved;
                    {
                        *pos = saved;
                        return false;
                    }
                }
            }
        }
        _ => {
            return false;
        }
    }
}
fn parse_Proc_impl<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
    stack: &mut Vec<Frame_Proc>,
) -> Result<Proc, ParseError> {
    stack.clear();
    let mut cur_bp = min_bp;
    'drive: loop {
        FRAME_STATE_PROC
            .with(|c| c.set((stack.len() as u16, frame_kind_of_Proc(stack))));
        let mut lhs: Proc = 'prefix: {
            if *pos >= tokens.len() {
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero());
                match stack.pop() {
                    None => {
                        return Err(ParseError::UnexpectedEof {
                            expected: Cow::Borrowed(
                                "Proc expression (one of: \"Caret\", \"DdollarNameLp\", \"DdollarProcLp\", \"DollarName\", \"DollarProc\", \"Kw0\", ... [13 options])",
                            ),
                            range: eof_range,
                            hint: None,
                        });
                    }
                    Some(
                        Frame_Proc::CollectionElem_PPar { elements, saved_pos, saved_bp },
                    ) => {
                        *pos = saved_pos;
                        if *pos < tokens.len() {
                            expect_token(
                                tokens,
                                pos,
                                |t| matches!(t, Token::RBrace),
                                "}",
                            )?;
                        }
                        cur_bp = saved_bp;
                        break 'prefix Proc::PPar(elements);
                    }
                    Some(_) => {
                        return Err(ParseError::UnexpectedEof {
                            expected: Cow::Borrowed(
                                "Proc expression (one of: \"Caret\", \"DdollarNameLp\", \"DdollarProcLp\", \"DollarName\", \"DollarProc\", \"Kw0\", ... [13 options])",
                            ),
                            range: eof_range,
                            hint: None,
                        });
                    }
                }
            }
            {
                let forced = NFA_FORCED_PREFIX_PROC.with(|cell| cell.take());
                if let Some((forced_val, forced_pos, _forced_weight)) = forced {
                    *pos = forced_pos;
                    break 'prefix forced_val;
                }
            }
            {
                let mut __out = std::mem::MaybeUninit::<Proc>::uninit();
                if __cross_cat_dispatch_Proc(tokens, pos, &mut __out as *mut _, cur_bp) {
                    break 'prefix unsafe { __out.assume_init() };
                }
            }
            match &tokens[*pos].0 {
                Token::Kw0 => {
                    *pos += 1;
                    break 'prefix Proc::PZero;
                }
                Token::KwNew => {
                    *pos += 1;
                    expect_token(tokens, pos, |t| matches!(t, Token::LParen), "(")?;
                    let x = expect_ident(tokens, pos)?;
                    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
                    stack
                        .push(Frame_Proc::RD_PNew_0 {
                            saved_bp: cur_bp,
                            x,
                        });
                    cur_bp = 0;
                    continue 'drive;
                }
                Token::Tok_69_6e_28 => {
                    *pos += 1;
                    let name = parse_Name(tokens, pos, 0)?;
                    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
                    stack
                        .push(Frame_Proc::RD_PIn_0 {
                            saved_bp: cur_bp,
                            name,
                        });
                    cur_bp = 0;
                    continue 'drive;
                }
                Token::Tok_6f_70_65_6e_28 => {
                    *pos += 1;
                    let name = parse_Name(tokens, pos, 0)?;
                    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
                    stack
                        .push(Frame_Proc::RD_POpen_0 {
                            saved_bp: cur_bp,
                            name,
                        });
                    cur_bp = 0;
                    continue 'drive;
                }
                Token::Tok_6f_75_74_28 => {
                    *pos += 1;
                    let name = parse_Name(tokens, pos, 0)?;
                    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
                    stack
                        .push(Frame_Proc::RD_POut_0 {
                            saved_bp: cur_bp,
                            name,
                        });
                    cur_bp = 0;
                    continue 'drive;
                }
                Token::LBrace => {
                    *pos += 1;
                    stack
                        .push(Frame_Proc::CollectionElem_PPar {
                            elements: mettail_runtime::HashBag::new(),
                            saved_pos: *pos,
                            saved_bp: cur_bp,
                        });
                    cur_bp = 0;
                    continue 'drive;
                }
                Token::LParen => {
                    *pos += 1;
                    stack
                        .push(Frame_Proc::GroupClose {
                            saved_bp: cur_bp,
                        });
                    cur_bp = 0;
                    continue 'drive;
                }
                Token::Caret => {
                    *pos += 1;
                    match peek_token(tokens, *pos) {
                        Some(Token::LBracket) => {
                            *pos += 1;
                            let mut binder_names = Vec::with_capacity(4);
                            loop {
                                let name = expect_ident(tokens, pos)?;
                                binder_names.push(name);
                                if peek_token(tokens, *pos)
                                    .map_or(false, |t| matches!(t, Token::Comma))
                                {
                                    *pos += 1;
                                } else {
                                    break;
                                }
                            }
                            expect_token(
                                tokens,
                                pos,
                                |t| matches!(t, Token::RBracket),
                                "]",
                            )?;
                            expect_token(tokens, pos, |t| matches!(t, Token::Dot), ".")?;
                            expect_token(
                                tokens,
                                pos,
                                |t| matches!(t, Token::LBrace),
                                "{",
                            )?;
                            stack
                                .push(Frame_Proc::LambdaBody_Multi {
                                    binder_names,
                                    saved_bp: cur_bp,
                                });
                            cur_bp = 0;
                            continue 'drive;
                        }
                        Some(Token::Ident(_)) => {
                            let binder_name = expect_ident(tokens, pos)?;
                            expect_token(tokens, pos, |t| matches!(t, Token::Dot), ".")?;
                            expect_token(
                                tokens,
                                pos,
                                |t| matches!(t, Token::LBrace),
                                "{",
                            )?;
                            stack
                                .push(Frame_Proc::LambdaBody_Single {
                                    binder_name,
                                    saved_bp: cur_bp,
                                });
                            cur_bp = 0;
                            continue 'drive;
                        }
                        _ => {
                            return Err(ParseError::UnexpectedToken {
                                expected: Cow::Borrowed("identifier or '['"),
                                found: format_token_friendly(&tokens[*pos].0),
                                range: tokens[*pos].1,
                                hint: None,
                            });
                        }
                    }
                }
                Token::DollarProc => {
                    *pos += 1;
                    expect_token(tokens, pos, |t| matches!(t, Token::LParen), "(")?;
                    stack
                        .push(Frame_Proc::DollarF_Proc {
                            saved_bp: cur_bp,
                        });
                    cur_bp = 0;
                    continue 'drive;
                }
                Token::DdollarProcLp => {
                    *pos += 1;
                    stack
                        .push(Frame_Proc::DdollarF_Proc {
                            saved_bp: cur_bp,
                        });
                    cur_bp = 0;
                    continue 'drive;
                }
                Token::DollarName => {
                    *pos += 1;
                    expect_token(tokens, pos, |t| matches!(t, Token::LParen), "(")?;
                    stack
                        .push(Frame_Proc::DollarF_Name {
                            saved_bp: cur_bp,
                        });
                    cur_bp = 0;
                    continue 'drive;
                }
                Token::DdollarNameLp => {
                    *pos += 1;
                    stack
                        .push(Frame_Proc::DdollarF_Name {
                            saved_bp: cur_bp,
                        });
                    cur_bp = 0;
                    continue 'drive;
                }
                Token::Ident(name) => {
                    match peek_ahead(tokens, *pos, 1) {
                        Some(Token::LBracket) => {
                            match parse_pamb(tokens, pos) {
                                Ok(v) => break 'prefix v,
                                Err(e) => {
                                    match stack.pop() {
                                        None => return Err(e),
                                        Some(
                                            Frame_Proc::CollectionElem_PPar {
                                                elements,
                                                saved_pos,
                                                saved_bp,
                                            },
                                        ) => {
                                            *pos = saved_pos;
                                            expect_token(
                                                tokens,
                                                pos,
                                                |t| matches!(t, Token::RBrace),
                                                "}",
                                            )?;
                                            cur_bp = saved_bp;
                                            break 'prefix Proc::PPar(elements);
                                        }
                                        Some(_) => return Err(e),
                                    }
                                }
                            }
                        }
                        _ => {
                            let var_name = (*name).to_string();
                            *pos += 1;
                            break 'prefix Proc::PVar(
                                mettail_runtime::OrdVar(
                                    mettail_runtime::Var::Free(
                                        mettail_runtime::get_or_create_var(var_name),
                                    ),
                                ),
                            );
                        }
                    }
                }
                other => {
                    let err = Err(ParseError::UnexpectedToken {
                        expected: Cow::Borrowed(
                            "Proc expression (one of: \"Caret\", \"DdollarNameLp\", \"DdollarProcLp\", \"DollarName\", \"DollarProc\", \"Kw0\", ... [13 options])",
                        ),
                        found: format_token_friendly(other),
                        range: tokens[*pos].1,
                        hint: None,
                    });
                    match stack.pop() {
                        None => return err.map(|_: Proc| unreachable!()),
                        Some(
                            Frame_Proc::CollectionElem_PPar {
                                elements,
                                saved_pos,
                                saved_bp,
                            },
                        ) => {
                            *pos = saved_pos;
                            expect_token(
                                tokens,
                                pos,
                                |t| matches!(t, Token::RBrace),
                                "}",
                            )?;
                            cur_bp = saved_bp;
                            break 'prefix Proc::PPar(elements);
                        }
                        Some(_) => return err.map(|_: Proc| unreachable!()),
                    }
                }
            }
        };
        'unwind: loop {
            match stack.pop() {
                None => return Ok(lhs),
                Some(Frame_Proc::GroupClose { saved_bp }) => {
                    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
                    cur_bp = saved_bp;
                }
                Some(Frame_Proc::RD_PIn_0 { saved_bp, name }) => {
                    let proc = lhs;
                    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
                    lhs = Proc::PIn(Box::new(name), Box::new(proc));
                    cur_bp = saved_bp;
                }
                Some(Frame_Proc::RD_POut_0 { saved_bp, name }) => {
                    let proc = lhs;
                    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
                    lhs = Proc::POut(Box::new(name), Box::new(proc));
                    cur_bp = saved_bp;
                }
                Some(Frame_Proc::RD_POpen_0 { saved_bp, name }) => {
                    let proc = lhs;
                    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
                    lhs = Proc::POpen(Box::new(name), Box::new(proc));
                    cur_bp = saved_bp;
                }
                Some(Frame_Proc::RD_PNew_0 { saved_bp, x }) => {
                    let p = lhs;
                    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
                    lhs = Proc::PNew(
                        mettail_runtime::Scope::new(
                            mettail_runtime::Binder(
                                mettail_runtime::get_or_create_var(x),
                            ),
                            Box::new(p),
                        ),
                    );
                    cur_bp = saved_bp;
                }
                Some(
                    Frame_Proc::CollectionElem_PPar { mut elements, saved_pos, saved_bp },
                ) => {
                    elements.insert(lhs);
                    if peek_token(tokens, *pos)
                        .map_or(false, |t| matches!(t, Token::Pipe))
                    {
                        *pos += 1;
                        stack
                            .push(Frame_Proc::CollectionElem_PPar {
                                elements,
                                saved_pos: *pos,
                                saved_bp,
                            });
                        cur_bp = 0;
                        continue 'drive;
                    }
                    expect_token(tokens, pos, |t| matches!(t, Token::RBrace), "}")?;
                    lhs = Proc::PPar(elements);
                    cur_bp = saved_bp;
                }
                Some(Frame_Proc::LambdaBody_Single { binder_name, saved_bp }) => {
                    expect_token(tokens, pos, |t| matches!(t, Token::RBrace), "}")?;
                    let inferred = lhs.infer_var_type(&binder_name);
                    let scope = mettail_runtime::Scope::new(
                        mettail_runtime::Binder(
                            mettail_runtime::get_or_create_var(binder_name),
                        ),
                        Box::new(lhs),
                    );
                    lhs = match inferred {
                        Some(InferredType::Base(VarCategory::Proc)) => {
                            Proc::LamProc(scope)
                        }
                        Some(InferredType::Base(VarCategory::Name)) => {
                            Proc::LamName(scope)
                        }
                        _ => Proc::LamProc(scope),
                    };
                    cur_bp = saved_bp;
                }
                Some(Frame_Proc::LambdaBody_Multi { binder_names, saved_bp }) => {
                    expect_token(tokens, pos, |t| matches!(t, Token::RBrace), "}")?;
                    let inferred = if let Some(name) = binder_names.first() {
                        lhs.infer_var_type(name)
                    } else {
                        None
                    };
                    let binders: Vec<mettail_runtime::Binder<String>> = binder_names
                        .into_iter()
                        .map(|s| mettail_runtime::Binder(
                            mettail_runtime::get_or_create_var(s),
                        ))
                        .collect();
                    let scope = mettail_runtime::Scope::new(binders, Box::new(lhs));
                    lhs = match inferred {
                        Some(InferredType::Base(VarCategory::Proc)) => {
                            Proc::MLamProc(scope)
                        }
                        Some(InferredType::Base(VarCategory::Name)) => {
                            Proc::MLamName(scope)
                        }
                        _ => Proc::MLamProc(scope),
                    };
                    cur_bp = saved_bp;
                }
                Some(Frame_Proc::DollarF_Proc { saved_bp }) => {
                    let f = lhs;
                    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
                    let x = parse_Proc(tokens, pos, 0)?;
                    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
                    lhs = Proc::ApplyProc(Box::new(f), Box::new(x));
                    cur_bp = saved_bp;
                }
                Some(Frame_Proc::DdollarF_Proc { saved_bp }) => {
                    let f = lhs;
                    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
                    let mut args: Vec<Proc> = Vec::with_capacity(4);
                    loop {
                        let arg = parse_Proc(tokens, pos, 0)?;
                        args.push(arg);
                        if peek_token(tokens, *pos)
                            .map_or(false, |t| matches!(t, Token::Comma))
                        {
                            *pos += 1;
                        } else {
                            break;
                        }
                    }
                    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
                    lhs = Proc::MApplyProc(Box::new(f), args);
                    cur_bp = saved_bp;
                }
                Some(Frame_Proc::DollarF_Name { saved_bp }) => {
                    let f = lhs;
                    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
                    let x = parse_Name(tokens, pos, 0)?;
                    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
                    lhs = Proc::ApplyName(Box::new(f), Box::new(x));
                    cur_bp = saved_bp;
                }
                Some(Frame_Proc::DdollarF_Name { saved_bp }) => {
                    let f = lhs;
                    expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
                    let mut args: Vec<Name> = Vec::with_capacity(4);
                    loop {
                        let arg = parse_Name(tokens, pos, 0)?;
                        args.push(arg);
                        if peek_token(tokens, *pos)
                            .map_or(false, |t| matches!(t, Token::Comma))
                        {
                            *pos += 1;
                        } else {
                            break;
                        }
                    }
                    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
                    lhs = Proc::MApplyName(Box::new(f), args);
                    cur_bp = saved_bp;
                }
                Some(Frame_Proc::GuardEval { saved_bp }) => {
                    cur_bp = saved_bp;
                }
            }
        }
    }
}
/// Traced variant of `parse_Proc()` — emits `CekObserver` callbacks at each CEK transition point.
///
/// See [`mettail_prattail::cek::CekObserver`] for the observer trait.
#[allow(
    unused_mut,
    unused_variables,
    unused_assignments,
    unreachable_patterns,
    clippy::needless_return
)]
pub fn parse_Proc_traced<O: mettail_prattail::cek::CekObserver>(
    tokens: &[(Token, Range)],
    pos: &mut usize,
    min_bp: u8,
    __observer: &mut O,
) -> Result<Proc, String> {
    let mut __stack = FRAME_POOL_PROC.with(|c| c.take());
    __stack.clear();
    let mut cur_bp = min_bp;
    let mut lhs: Proc;
    let mut tail_wrap: Option<(u8, u8)> = None;
    let __start_pos = *pos;
    {
        let __evt = mettail_prattail::cek::CekStepEvent {
            rule: mettail_prattail::cek::TransitionRule::Drive,
            pos: *pos,
            cur_bp: cur_bp,
            stack_depth: __stack.len(),
            frame_variant: None,
            running_weight: 0.0,
            category: "Proc",
        };
        match __observer.on_event(&__evt) {
            mettail_prattail::cek::CekControl::Continue => {}
            mettail_prattail::cek::CekControl::Checkpoint => {
                let __cfg = mettail_prattail::cek::PdaConfiguration {
                    pos: *pos,
                    cur_bp: cur_bp,
                    stack_tags: __stack.iter().map(|f| format!("{:?}", f)).collect(),
                    phase: mettail_prattail::cek::CekState::PrefixDispatch {
                        pos: *pos,
                        cur_bp: cur_bp,
                    },
                };
                __observer.on_checkpoint(&__cfg);
            }
            mettail_prattail::cek::CekControl::Abort => {
                return Err(format!("parse aborted by observer at position {}", * pos));
            }
        }
    }
    let __pre_pos = *pos;
    let __pre_depth = __stack.len();
    let __batch_result = parse_Proc_impl(tokens, pos, min_bp, &mut __stack);
    let __post_depth = __stack.len();
    if __post_depth > __pre_depth {
        {
            let __evt = mettail_prattail::cek::CekStepEvent {
                rule: mettail_prattail::cek::TransitionRule::PrefixTerminalNt,
                pos: *pos,
                cur_bp: cur_bp,
                stack_depth: __stack.len(),
                frame_variant: None,
                running_weight: 0.0,
                category: "Proc",
            };
            match __observer.on_event(&__evt) {
                mettail_prattail::cek::CekControl::Continue => {}
                mettail_prattail::cek::CekControl::Checkpoint => {
                    let __cfg = mettail_prattail::cek::PdaConfiguration {
                        pos: *pos,
                        cur_bp: cur_bp,
                        stack_tags: __stack.iter().map(|f| format!("{:?}", f)).collect(),
                        phase: mettail_prattail::cek::CekState::PrefixDispatch {
                            pos: *pos,
                            cur_bp: cur_bp,
                        },
                    };
                    __observer.on_checkpoint(&__cfg);
                }
                mettail_prattail::cek::CekControl::Abort => {
                    return Err(
                        format!("parse aborted by observer at position {}", * pos),
                    );
                }
            }
        }
    } else if __post_depth < __pre_depth {
        {
            let __evt = mettail_prattail::cek::CekStepEvent {
                rule: mettail_prattail::cek::TransitionRule::UnwindInfix,
                pos: *pos,
                cur_bp: cur_bp,
                stack_depth: __stack.len(),
                frame_variant: None,
                running_weight: 0.0,
                category: "Proc",
            };
            match __observer.on_event(&__evt) {
                mettail_prattail::cek::CekControl::Continue => {}
                mettail_prattail::cek::CekControl::Checkpoint => {
                    let __cfg = mettail_prattail::cek::PdaConfiguration {
                        pos: *pos,
                        cur_bp: cur_bp,
                        stack_tags: __stack.iter().map(|f| format!("{:?}", f)).collect(),
                        phase: mettail_prattail::cek::CekState::PrefixDispatch {
                            pos: *pos,
                            cur_bp: cur_bp,
                        },
                    };
                    __observer.on_checkpoint(&__cfg);
                }
                mettail_prattail::cek::CekControl::Abort => {
                    return Err(
                        format!("parse aborted by observer at position {}", * pos),
                    );
                }
            }
        }
    } else if __pre_pos != *pos {
        {
            let __evt = mettail_prattail::cek::CekStepEvent {
                rule: mettail_prattail::cek::TransitionRule::Infix,
                pos: *pos,
                cur_bp: cur_bp,
                stack_depth: __stack.len(),
                frame_variant: None,
                running_weight: 0.0,
                category: "Proc",
            };
            match __observer.on_event(&__evt) {
                mettail_prattail::cek::CekControl::Continue => {}
                mettail_prattail::cek::CekControl::Checkpoint => {
                    let __cfg = mettail_prattail::cek::PdaConfiguration {
                        pos: *pos,
                        cur_bp: cur_bp,
                        stack_tags: __stack.iter().map(|f| format!("{:?}", f)).collect(),
                        phase: mettail_prattail::cek::CekState::PrefixDispatch {
                            pos: *pos,
                            cur_bp: cur_bp,
                        },
                    };
                    __observer.on_checkpoint(&__cfg);
                }
                mettail_prattail::cek::CekControl::Abort => {
                    return Err(
                        format!("parse aborted by observer at position {}", * pos),
                    );
                }
            }
        }
    }
    if __batch_result.is_ok() {
        {
            let __evt = mettail_prattail::cek::CekStepEvent {
                rule: mettail_prattail::cek::TransitionRule::UnwindEmpty,
                pos: *pos,
                cur_bp: cur_bp,
                stack_depth: 0,
                frame_variant: None,
                running_weight: 0.0,
                category: "Proc",
            };
            match __observer.on_event(&__evt) {
                mettail_prattail::cek::CekControl::Continue => {}
                mettail_prattail::cek::CekControl::Checkpoint => {
                    let __cfg = mettail_prattail::cek::PdaConfiguration {
                        pos: *pos,
                        cur_bp: cur_bp,
                        stack_tags: __stack.iter().map(|f| format!("{:?}", f)).collect(),
                        phase: mettail_prattail::cek::CekState::PrefixDispatch {
                            pos: *pos,
                            cur_bp: cur_bp,
                        },
                    };
                    __observer.on_checkpoint(&__cfg);
                }
                mettail_prattail::cek::CekControl::Abort => {
                    return Err(
                        format!("parse aborted by observer at position {}", * pos),
                    );
                }
            }
        }
    }
    FRAME_POOL_PROC.with(|c| c.set(__stack));
    __batch_result.map_err(|e| format!("{:?}", e))
}
#[derive(Debug)]
enum Frame_Name {
    GroupClose { saved_bp: u8 },
    GuardEval { saved_bp: u8 },
}
thread_local! {
    static FRAME_POOL_NAME : std::cell::Cell < Vec < Frame_Name >> =
    std::cell::Cell::new(Vec::with_capacity(2));
}
thread_local! {
    static FRAME_STATE_NAME : std::cell::Cell < (u16, u8) > = std::cell::Cell::new((0,
    9));
}
fn frame_kind_of_Name(stack: &[Frame_Name]) -> u8 {
    match stack.last() {
        Some(Frame_Name::GroupClose { .. }) => 4_u8,
        Some(Frame_Name::GuardEval { .. }) => 9_u8,
        None => 9_u8,
    }
}
thread_local! {
    static NFA_PREFIX_SPILL_NAME : std::cell::Cell < Vec < (Name, usize, f64) >> =
    std::cell::Cell::new(Vec::new()); static NFA_FORCED_PREFIX_NAME : std::cell::Cell <
    Option < (Name, usize, f64) >> = std::cell::Cell::new(None); static
    NFA_PRIMARY_WEIGHT_NAME : std::cell::Cell < f64 > = std::cell::Cell::new(0.5); static
    RUNNING_WEIGHT_NAME : std::cell::Cell < f64 > = std::cell::Cell::new(0.0); static
    PARENT_WEIGHT_NAME : std::cell::Cell < f64 > = std::cell::Cell::new(0.0);
}
#[inline]
pub fn running_weight_Name() -> f64 {
    RUNNING_WEIGHT_NAME.with(|cell| cell.get())
}
fn parse_Name<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
) -> Result<Name, ParseError> {
    RUNNING_WEIGHT_NAME
        .with(|cell| {
            let inherited = PARENT_WEIGHT_NAME
                .with(|p| {
                    let v = p.get();
                    p.set(0.0);
                    v
                });
            cell.set(inherited);
        });
    FRAME_POOL_NAME
        .with(|cell| {
            let mut stack = cell.take();
            let needed = tokens.len() / 2;
            if stack.capacity() < needed {
                stack.reserve(needed - stack.len());
            }
            let result = parse_Name_impl(tokens, pos, min_bp, &mut stack);
            cell.set(stack);
            result
        })
}
fn parse_Name_impl<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
    stack: &mut Vec<Frame_Name>,
) -> Result<Name, ParseError> {
    stack.clear();
    let mut cur_bp = min_bp;
    'drive: loop {
        FRAME_STATE_NAME
            .with(|c| c.set((stack.len() as u16, frame_kind_of_Name(stack))));
        let mut lhs: Name = 'prefix: {
            if *pos >= tokens.len() {
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero());
                match stack.pop() {
                    None => {
                        return Err(ParseError::UnexpectedEof {
                            expected: Cow::Borrowed(
                                "Name expression (one of: \"LParen\", identifier)",
                            ),
                            range: eof_range,
                            hint: None,
                        });
                    }
                    Some(_) => {
                        return Err(ParseError::UnexpectedEof {
                            expected: Cow::Borrowed(
                                "Name expression (one of: \"LParen\", identifier)",
                            ),
                            range: eof_range,
                            hint: None,
                        });
                    }
                }
            }
            {
                let forced = NFA_FORCED_PREFIX_NAME.with(|cell| cell.take());
                if let Some((forced_val, forced_pos, _forced_weight)) = forced {
                    *pos = forced_pos;
                    break 'prefix forced_val;
                }
            }
            match &tokens[*pos].0 {
                Token::LParen => {
                    *pos += 1;
                    stack
                        .push(Frame_Name::GroupClose {
                            saved_bp: cur_bp,
                        });
                    cur_bp = 0;
                    continue 'drive;
                }
                Token::Ident(name) => {
                    let var_name = (*name).to_string();
                    *pos += 1;
                    break 'prefix Name::NVar(
                        mettail_runtime::OrdVar(
                            mettail_runtime::Var::Free(
                                mettail_runtime::get_or_create_var(var_name),
                            ),
                        ),
                    );
                }
                other => {
                    let found_str = format_token_friendly(other);
                    let source_cat: Option<&str> = match other {
                        Token::Caret
                        | Token::DdollarNameLp
                        | Token::DdollarProcLp
                        | Token::DollarName
                        | Token::DollarProc
                        | Token::Kw0
                        | Token::KwNew
                        | Token::LBrace
                        | Token::Tok_69_6e_28
                        | Token::Tok_6f_70_65_6e_28
                        | Token::Tok_6f_75_74_28 => Some("Proc"),
                        _ => None,
                    };
                    let expected_msg = match source_cat {
                        Some(sc) => {
                            Cow::Owned(
                                format!(
                                    "Name expression (one of: \"LParen\", identifier) Hint: this is a {} expression, but no {} → Name cast rule exists.",
                                    sc, sc
                                ),
                            )
                        }
                        None => {
                            Cow::Borrowed(
                                "Name expression (one of: \"LParen\", identifier)",
                            )
                        }
                    };
                    let err = Err(ParseError::UnexpectedToken {
                        expected: expected_msg,
                        found: found_str,
                        range: tokens[*pos].1,
                        hint: None,
                    });
                    match stack.pop() {
                        None => return err.map(|_: Name| unreachable!()),
                        Some(_) => return err.map(|_: Name| unreachable!()),
                    }
                }
            }
        };
        'unwind: loop {
            match stack.pop() {
                None => return Ok(lhs),
                Some(Frame_Name::GroupClose { saved_bp }) => {
                    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
                    cur_bp = saved_bp;
                }
                Some(Frame_Name::GuardEval { saved_bp }) => {
                    cur_bp = saved_bp;
                }
            }
        }
    }
}
fn sync_to<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    sync: &dyn Fn(&Token) -> bool,
) {
    while *pos < tokens.len() {
        if sync(&tokens[*pos].0) {
            return;
        }
        *pos += 1;
    }
}
fn expect_token_rec<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    predicate: impl Fn(&Token) -> bool,
    expected: &'static str,
    errors: &mut Vec<ParseError>,
) -> bool {
    if *pos >= tokens.len() {
        let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero());
        errors
            .push(ParseError::UnexpectedEof {
                expected: Cow::Borrowed(expected),
                range: eof_range,
                hint: None,
            });
        return false;
    }
    if predicate(&tokens[*pos].0) {
        *pos += 1;
        true
    } else {
        errors
            .push(ParseError::UnexpectedToken {
                expected: Cow::Borrowed(expected),
                found: format_token_friendly(&tokens[*pos].0),
                range: tokens[*pos].1,
                hint: None,
            });
        false
    }
}
fn expect_ident_rec<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    errors: &mut Vec<ParseError>,
) -> String {
    if *pos >= tokens.len() {
        let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero());
        errors
            .push(ParseError::UnexpectedEof {
                expected: Cow::Borrowed("identifier"),
                range: eof_range,
                hint: None,
            });
        return "__error__".to_string();
    }
    match &tokens[*pos].0 {
        Token::Ident(name) => {
            let result = name.to_string();
            *pos += 1;
            result
        }
        other => {
            errors
                .push(ParseError::UnexpectedToken {
                    expected: Cow::Borrowed("identifier"),
                    found: format_token_friendly(other),
                    range: tokens[*pos].1,
                    hint: Some(
                        Cow::Borrowed(
                            "expected a variable name, not a keyword or operator",
                        ),
                    ),
                });
            "__error__".to_string()
        }
    }
}
fn is_sync_Proc<'a>(token: &Token<'a>) -> bool {
    matches!(
        token, Token::Eof | Token::RParen | Token::RBrace | Token::RBracket |
        Token::Comma | Token::Pipe
    )
}
/// WFST-based 4-strategy context-aware recovery for category `Proc`.
///
/// Evaluates skip-to-sync, delete, insert, and substitute strategies with
/// context-aware cost adjustments from nesting depth, binding power,
/// frame kind, and bracket balance.
fn wfst_recover_Proc<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    depth: usize,
    binding_power: u8,
    open_parens: u16,
    open_braces: u16,
    open_brackets: u16,
) -> Option<String> {
    let start = *pos;
    let remaining = tokens.len() - start;
    let max_look = if remaining < 32 { remaining } else { 32 };
    let mut best_pos: Option<usize> = None;
    let mut best_cost: f64 = f64::INFINITY;
    let mut best_desc: String = String::new();
    let (frame_depth, frame_kind) = FRAME_STATE_PROC.with(|c| c.get());
    let effective_depth = if frame_depth > 0 { frame_depth as usize } else { depth };
    let skip_mult: f64 = if effective_depth > 1000 {
        0.5
    } else if effective_depth < 10 {
        2.0
    } else {
        1.0
    };
    let bp_mult: f64 = if binding_power < 4 { 0.75 } else { 1.0 };
    let frame_skip_mult: f64 = if frame_kind == 1 { 0.75 } else { 1.0 };
    let combined_skip_mult = skip_mult * bp_mult * frame_skip_mult
        * {
            let rw = RUNNING_WEIGHT_PROC.with(|c| c.get());
            if rw < 1.0 { 0.75 } else { 1.0 }
        };
    let adaptive_insert_mult: f64 = {
        let rw = RUNNING_WEIGHT_PROC.with(|c| c.get());
        if rw >= 1.0 { 0.5 } else { 1.0 }
    };
    for skip in 0..max_look {
        let idx = start + skip;
        if matches!(
            & tokens[idx].0, Token::Comma | Token::Eof | Token::Pipe | Token::RBrace |
            Token::RBracket | Token::RParen
        ) {
            let cost = (skip as f64) * 0.5 * combined_skip_mult;
            if cost < best_cost {
                best_cost = cost;
                best_pos = Some(idx);
                best_desc = format!("skip {} token(s) to '{:?}'", skip, & tokens[idx].0);
            }
            break;
        }
    }
    if remaining > 0 {
        let cost = 1.0 * combined_skip_mult;
        if cost < best_cost {
            best_cost = cost;
            best_pos = Some(start + 1);
            best_desc = "delete unexpected token".to_string();
        }
    }
    {
        let frame_insert_mult: f64 = if frame_kind == 3 || frame_kind == 4 {
            0.5
        } else {
            1.0
        };
        let base_insert = 2.0_f64 * frame_insert_mult * adaptive_insert_mult;
        if open_parens > 0 {
            let cost = base_insert * 0.3;
            if cost < best_cost {
                best_cost = cost;
                best_pos = Some(start);
                best_desc = "insert missing ')'".to_string();
            }
        }
        if open_braces > 0 {
            let cost = base_insert * 0.3;
            if cost < best_cost {
                best_cost = cost;
                best_pos = Some(start);
                best_desc = "insert missing '}'".to_string();
            }
        }
        if open_brackets > 0 {
            let cost = base_insert * 0.3;
            if cost < best_cost {
                best_cost = cost;
                best_pos = Some(start);
                best_desc = "insert missing ']'".to_string();
            }
        }
    }
    if remaining > 0 {
        let sub_mult: f64 = if frame_kind == 5 { 0.75 } else { 1.0 };
        let cost = 1.5 * sub_mult;
        if cost < best_cost {
            best_cost = cost;
            best_pos = Some(start + 1);
            best_desc = "substitute unexpected token".to_string();
        }
    }
    if let Some(new_pos) = best_pos {
        let sim_ids: Vec<u16> = tokens[new_pos..]
            .iter()
            .map(|(t, _)| token_to_id(t))
            .collect();
        let sim_result = PARSE_SIMULATOR.simulate_after_repair(&sim_ids, 0, "Proc");
        let sim_mult = PARSE_SIMULATOR.cost_multiplier(&sim_result);
        best_cost *= sim_mult;
    }
    {
        let all_ids: Vec<u16> = tokens[start..]
            .iter()
            .map(|(t, _)| token_to_id(t))
            .collect();
        let sync_set: std::collections::BTreeSet<u16> = RECOVERY_SYNC_TOKENS_Proc
            .iter()
            .copied()
            .collect();
        if let Some(seq) = mettail_prattail::recovery::viterbi_multi_step(
            &all_ids,
            0,
            &sync_set,
            &mettail_prattail::recovery::RecoveryConfig::default(),
        ) {
            let multi_cost = seq.total_cost.left.value();
            if multi_cost < best_cost {
                best_cost = multi_cost;
                best_pos = Some(start + seq.new_pos);
                best_desc = format!(
                    "{} action(s): {}", seq.actions.len(), seq.actions.iter().map(| a |
                    format!("{:?}", a)).collect::< Vec < _ >> ().join(", ")
                );
            }
        }
    }
    match best_pos {
        Some(new_pos) => {
            *pos = new_pos;
            Some(best_desc)
        }
        None => None,
    }
}
thread_local! {
    static BRACKET_STATE_Proc : std::cell::Cell < (usize, u16, u16, u16) > =
    std::cell::Cell::new((0, 0, 0, 0)); static LAST_ERROR_POS_Proc : std::cell::Cell <
    usize > = std::cell::Cell::new(usize::MAX);
}
fn parse_Proc_recovering<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
    errors: &mut Vec<ParseError>,
) -> Option<Proc> {
    if min_bp == 0 {
        BRACKET_STATE_Proc.with(|c| c.set((0, 0, 0, 0)));
        LAST_ERROR_POS_Proc.with(|c| c.set(usize::MAX));
    }
    match parse_Proc(tokens, pos, min_bp) {
        Ok(v) => Some(v),
        Err(e) => {
            let last_err = LAST_ERROR_POS_Proc.with(|c| c.get());
            if last_err != usize::MAX && *pos <= last_err + 3 {
                if *pos < tokens.len() {
                    *pos += 1;
                }
                return None;
            }
            LAST_ERROR_POS_Proc.with(|c| c.set(*pos));
            let (op, ob, ok) = BRACKET_STATE_Proc
                .with(|c| {
                    let (last, mut op, mut ob, mut ok) = c.get();
                    let scan_to = if *pos < tokens.len() { *pos } else { tokens.len() };
                    for i in last..scan_to {
                        match &tokens[i].0 {
                            Token::RBracket => ok = ok.saturating_sub(1),
                            _ => {}
                        }
                    }
                    c.set((scan_to, op, ob, ok));
                    (op, ob, ok)
                });
            let repair_range = e.range();
            match wfst_recover_Proc(tokens, pos, 0, min_bp, op, ob, ok) {
                Some(desc) => {
                    errors
                        .push(ParseError::RecoveryApplied {
                            original_error: Box::new(e),
                            repair_description: desc,
                            range: repair_range,
                        })
                }
                None => errors.push(e),
            }
            None
        }
    }
}
fn is_sync_Name<'a>(token: &Token<'a>) -> bool {
    matches!(
        token, Token::Eof | Token::RParen | Token::RBrace | Token::RBracket |
        Token::Comma | Token::LBracket
    )
}
/// WFST-based 4-strategy context-aware recovery for category `Name`.
///
/// Evaluates skip-to-sync, delete, insert, and substitute strategies with
/// context-aware cost adjustments from nesting depth, binding power,
/// frame kind, and bracket balance.
fn wfst_recover_Name<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    depth: usize,
    binding_power: u8,
    open_parens: u16,
    open_braces: u16,
    open_brackets: u16,
) -> Option<String> {
    let start = *pos;
    let remaining = tokens.len() - start;
    let max_look = if remaining < 32 { remaining } else { 32 };
    let mut best_pos: Option<usize> = None;
    let mut best_cost: f64 = f64::INFINITY;
    let mut best_desc: String = String::new();
    let (frame_depth, frame_kind) = FRAME_STATE_NAME.with(|c| c.get());
    let effective_depth = if frame_depth > 0 { frame_depth as usize } else { depth };
    let skip_mult: f64 = if effective_depth > 1000 {
        0.5
    } else if effective_depth < 10 {
        2.0
    } else {
        1.0
    };
    let bp_mult: f64 = if binding_power < 4 { 0.75 } else { 1.0 };
    let frame_skip_mult: f64 = if frame_kind == 1 { 0.75 } else { 1.0 };
    let combined_skip_mult = skip_mult * bp_mult * frame_skip_mult
        * {
            let rw = RUNNING_WEIGHT_NAME.with(|c| c.get());
            if rw < 1.0 { 0.75 } else { 1.0 }
        };
    let adaptive_insert_mult: f64 = {
        let rw = RUNNING_WEIGHT_NAME.with(|c| c.get());
        if rw >= 1.0 { 0.5 } else { 1.0 }
    };
    for skip in 0..max_look {
        let idx = start + skip;
        if matches!(
            & tokens[idx].0, Token::Comma | Token::Eof | Token::LBracket | Token::RBrace
            | Token::RBracket | Token::RParen
        ) {
            let cost = (skip as f64) * 0.5 * combined_skip_mult;
            if cost < best_cost {
                best_cost = cost;
                best_pos = Some(idx);
                best_desc = format!("skip {} token(s) to '{:?}'", skip, & tokens[idx].0);
            }
            break;
        }
    }
    if remaining > 0 {
        let cost = 1.0 * combined_skip_mult;
        if cost < best_cost {
            best_cost = cost;
            best_pos = Some(start + 1);
            best_desc = "delete unexpected token".to_string();
        }
    }
    {
        let frame_insert_mult: f64 = if frame_kind == 3 || frame_kind == 4 {
            0.5
        } else {
            1.0
        };
        let base_insert = 2.0_f64 * frame_insert_mult * adaptive_insert_mult;
        if open_parens > 0 {
            let cost = base_insert * 0.3;
            if cost < best_cost {
                best_cost = cost;
                best_pos = Some(start);
                best_desc = "insert missing ')'".to_string();
            }
        }
        if open_braces > 0 {
            let cost = base_insert * 0.3;
            if cost < best_cost {
                best_cost = cost;
                best_pos = Some(start);
                best_desc = "insert missing '}'".to_string();
            }
        }
        if open_brackets > 0 {
            let cost = base_insert * 0.3;
            if cost < best_cost {
                best_cost = cost;
                best_pos = Some(start);
                best_desc = "insert missing ']'".to_string();
            }
        }
    }
    if remaining > 0 {
        let sub_mult: f64 = if frame_kind == 5 { 0.75 } else { 1.0 };
        let cost = 1.5 * sub_mult;
        if cost < best_cost {
            best_cost = cost;
            best_pos = Some(start + 1);
            best_desc = "substitute unexpected token".to_string();
        }
    }
    if let Some(new_pos) = best_pos {
        let sim_ids: Vec<u16> = tokens[new_pos..]
            .iter()
            .map(|(t, _)| token_to_id(t))
            .collect();
        let sim_result = PARSE_SIMULATOR.simulate_after_repair(&sim_ids, 0, "Name");
        let sim_mult = PARSE_SIMULATOR.cost_multiplier(&sim_result);
        best_cost *= sim_mult;
    }
    {
        let all_ids: Vec<u16> = tokens[start..]
            .iter()
            .map(|(t, _)| token_to_id(t))
            .collect();
        let sync_set: std::collections::BTreeSet<u16> = RECOVERY_SYNC_TOKENS_Name
            .iter()
            .copied()
            .collect();
        if let Some(seq) = mettail_prattail::recovery::viterbi_multi_step(
            &all_ids,
            0,
            &sync_set,
            &mettail_prattail::recovery::RecoveryConfig::default(),
        ) {
            let multi_cost = seq.total_cost.left.value();
            if multi_cost < best_cost {
                best_cost = multi_cost;
                best_pos = Some(start + seq.new_pos);
                best_desc = format!(
                    "{} action(s): {}", seq.actions.len(), seq.actions.iter().map(| a |
                    format!("{:?}", a)).collect::< Vec < _ >> ().join(", ")
                );
            }
        }
    }
    match best_pos {
        Some(new_pos) => {
            *pos = new_pos;
            Some(best_desc)
        }
        None => None,
    }
}
thread_local! {
    static BRACKET_STATE_Name : std::cell::Cell < (usize, u16, u16, u16) > =
    std::cell::Cell::new((0, 0, 0, 0)); static LAST_ERROR_POS_Name : std::cell::Cell <
    usize > = std::cell::Cell::new(usize::MAX);
}
fn parse_Name_recovering<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
    errors: &mut Vec<ParseError>,
) -> Option<Name> {
    if min_bp == 0 {
        BRACKET_STATE_Name.with(|c| c.set((0, 0, 0, 0)));
        LAST_ERROR_POS_Name.with(|c| c.set(usize::MAX));
    }
    match parse_Name(tokens, pos, min_bp) {
        Ok(v) => Some(v),
        Err(e) => {
            let last_err = LAST_ERROR_POS_Name.with(|c| c.get());
            if last_err != usize::MAX && *pos <= last_err + 3 {
                if *pos < tokens.len() {
                    *pos += 1;
                }
                return None;
            }
            LAST_ERROR_POS_Name.with(|c| c.set(*pos));
            let (op, ob, ok) = BRACKET_STATE_Name
                .with(|c| {
                    let (last, mut op, mut ob, mut ok) = c.get();
                    let scan_to = if *pos < tokens.len() { *pos } else { tokens.len() };
                    for i in last..scan_to {
                        match &tokens[i].0 {
                            Token::RBracket => ok = ok.saturating_sub(1),
                            _ => {}
                        }
                    }
                    c.set((scan_to, op, ob, ok));
                    (op, ob, ok)
                });
            let repair_range = e.range();
            match wfst_recover_Name(tokens, pos, 0, min_bp, op, ob, ok) {
                Some(desc) => {
                    errors
                        .push(ParseError::RecoveryApplied {
                            original_error: Box::new(e),
                            repair_description: desc,
                            range: repair_range,
                        })
                }
                None => errors.push(e),
            }
            None
        }
    }
}
impl Proc {
    /// Parse a string as this category.
    ///
    /// Returns `Err(String)` with a human-readable error message including
    /// line:column position on parse failure.
    pub fn parse(input: &str) -> Result<Proc, std::string::String> {
        Self::parse_structured(input).map_err(|e| e.to_string())
    }
    /// Parse a string as this category, returning a structured `ParseError`.
    ///
    /// The `ParseError` carries the exact source position (`Range` with
    /// `Position { byte_offset, line, column }`) and a descriptive message.
    /// Use this for programmatic error handling (IDE integration, error recovery).
    ///
    /// Zero-copy: the lexer produces `Token<'a>` borrowing from `input`,
    /// so no String allocations occur during lexing.
    pub fn parse_structured(input: &str) -> Result<Proc, ParseError> {
        let tokens = lex(input)?;
        let mut pos = 0usize;
        let result = parse_Proc(&tokens, &mut pos, 0)?;
        if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
            return Err(ParseError::TrailingTokens {
                found: format_token_friendly(&tokens[pos].0),
                range: tokens[pos].1,
                hint: Some(
                    Cow::Borrowed(
                        "the parser finished but input remains; check for missing operators or extra tokens",
                    ),
                ),
            });
        }
        Ok(result)
    }
    /// Parse a string with source-context error messages.
    ///
    /// On error, includes a source snippet with caret pointing to the
    /// error location (rustc-style). The source is used for display only;
    /// parsing operates on `input`.
    pub fn parse_with_source(input: &str) -> Result<Proc, std::string::String> {
        Self::parse_structured(input)
            .map_err(|e| {
                let range = e.range();
                format!("{}\n{}", e, format_error_context(input, & range))
            })
    }
    /// Parse with error recovery, collecting multiple errors.
    ///
    /// Unlike `parse()` which stops at the first error, this continues
    /// parsing after errors using panic-mode recovery with FOLLOW-set-based
    /// synchronization points.
    ///
    /// Returns `(Option<ast>, errors)` where:
    /// - `Some(ast)` with empty errors: successful parse
    /// - `Some(ast)` with errors: partial result with recovered errors
    /// - `None` with errors: unrecoverable (e.g., lex error or prefix failure)
    pub fn parse_recovering(input: &str) -> (Option<Proc>, Vec<ParseError>) {
        let tokens = match lex(input) {
            Ok(t) => t,
            Err(e) => return (None, vec![ParseError::from(e)]),
        };
        let mut pos = 0usize;
        let mut errors = Vec::new();
        let result = parse_Proc_recovering(&tokens, &mut pos, 0, &mut errors);
        if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
            errors
                .push(ParseError::TrailingTokens {
                    found: format_token_friendly(&tokens[pos].0),
                    range: tokens[pos].1,
                    hint: Some(
                        Cow::Borrowed(
                            "the parser finished but input remains; check for missing operators or extra tokens",
                        ),
                    ),
                });
        }
        (result, errors)
    }
    /// Parse with weight emission: calls `lex_weighted()` to get
    /// per-token tropical weights, then parses normally.
    ///
    /// Returns `(result, weights)` where `weights[i]` is the tropical
    /// weight (lower = higher priority) for `tokens[i]`.
    ///
    /// Requires the `wfst` feature.
    pub fn parse_structured_weighted(
        input: &str,
    ) -> Result<(Proc, Vec<f64>), ParseError> {
        let weighted_tokens = lex_weighted(input)?;
        let weights: Vec<f64> = weighted_tokens.iter().map(|(_, _, w)| *w).collect();
        let tokens: Vec<(Token<'_>, Range)> = weighted_tokens
            .into_iter()
            .map(|(t, r, _)| (t, r))
            .collect();
        let mut pos = 0usize;
        let result = parse_Proc(&tokens, &mut pos, 0)?;
        if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
            return Err(ParseError::TrailingTokens {
                found: format_token_friendly(&tokens[pos].0),
                range: tokens[pos].1,
                hint: Some(
                    Cow::Borrowed(
                        "the parser finished but input remains; check for missing operators or extra tokens",
                    ),
                ),
            });
        }
        Ok((result, weights))
    }
    /// B4: Parse with confidence scoring.
    ///
    /// Returns `(ast, confidence)` where `confidence` is the accumulated
    /// tropical weight of dispatch decisions along the parse path.
    ///
    /// **Interpretation:**
    /// - `0.0` — fully deterministic parse (no ambiguity encountered)
    /// - Low values (< 1.0) — mostly deterministic with minor ambiguity
    /// - High values (> 2.0) — significant ambiguity encountered
    ///
    /// Useful for language servers and IDE integration to flag low-confidence
    /// parses (e.g., display "ambiguous parse" diagnostics).
    pub fn parse_with_confidence(input: &str) -> Result<(Proc, f64), ParseError> {
        let tokens = lex(input)?;
        let mut pos = 0usize;
        let result = parse_Proc(&tokens, &mut pos, 0)?;
        if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
            return Err(ParseError::TrailingTokens {
                found: format_token_friendly(&tokens[pos].0),
                range: tokens[pos].1,
                hint: Some(
                    Cow::Borrowed(
                        "the parser finished but input remains; check for missing operators or extra tokens",
                    ),
                ),
            });
        }
        let confidence = running_weight_Proc();
        Ok((result, confidence))
    }
}
impl Name {
    /// Parse a string as this category.
    ///
    /// Returns `Err(String)` with a human-readable error message including
    /// line:column position on parse failure.
    pub fn parse(input: &str) -> Result<Name, std::string::String> {
        Self::parse_structured(input).map_err(|e| e.to_string())
    }
    /// Parse a string as this category, returning a structured `ParseError`.
    ///
    /// The `ParseError` carries the exact source position (`Range` with
    /// `Position { byte_offset, line, column }`) and a descriptive message.
    /// Use this for programmatic error handling (IDE integration, error recovery).
    ///
    /// Zero-copy: the lexer produces `Token<'a>` borrowing from `input`,
    /// so no String allocations occur during lexing.
    pub fn parse_structured(input: &str) -> Result<Name, ParseError> {
        let tokens = lex(input)?;
        let mut pos = 0usize;
        let result = parse_Name(&tokens, &mut pos, 0)?;
        if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
            return Err(ParseError::TrailingTokens {
                found: format_token_friendly(&tokens[pos].0),
                range: tokens[pos].1,
                hint: Some(
                    Cow::Borrowed(
                        "the parser finished but input remains; check for missing operators or extra tokens",
                    ),
                ),
            });
        }
        Ok(result)
    }
    /// Parse a string with source-context error messages.
    ///
    /// On error, includes a source snippet with caret pointing to the
    /// error location (rustc-style). The source is used for display only;
    /// parsing operates on `input`.
    pub fn parse_with_source(input: &str) -> Result<Name, std::string::String> {
        Self::parse_structured(input)
            .map_err(|e| {
                let range = e.range();
                format!("{}\n{}", e, format_error_context(input, & range))
            })
    }
    /// Parse with error recovery, collecting multiple errors.
    ///
    /// Unlike `parse()` which stops at the first error, this continues
    /// parsing after errors using panic-mode recovery with FOLLOW-set-based
    /// synchronization points.
    ///
    /// Returns `(Option<ast>, errors)` where:
    /// - `Some(ast)` with empty errors: successful parse
    /// - `Some(ast)` with errors: partial result with recovered errors
    /// - `None` with errors: unrecoverable (e.g., lex error or prefix failure)
    pub fn parse_recovering(input: &str) -> (Option<Name>, Vec<ParseError>) {
        let tokens = match lex(input) {
            Ok(t) => t,
            Err(e) => return (None, vec![ParseError::from(e)]),
        };
        let mut pos = 0usize;
        let mut errors = Vec::new();
        let result = parse_Name_recovering(&tokens, &mut pos, 0, &mut errors);
        if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
            errors
                .push(ParseError::TrailingTokens {
                    found: format_token_friendly(&tokens[pos].0),
                    range: tokens[pos].1,
                    hint: Some(
                        Cow::Borrowed(
                            "the parser finished but input remains; check for missing operators or extra tokens",
                        ),
                    ),
                });
        }
        (result, errors)
    }
    /// Parse with weight emission: calls `lex_weighted()` to get
    /// per-token tropical weights, then parses normally.
    ///
    /// Returns `(result, weights)` where `weights[i]` is the tropical
    /// weight (lower = higher priority) for `tokens[i]`.
    ///
    /// Requires the `wfst` feature.
    pub fn parse_structured_weighted(
        input: &str,
    ) -> Result<(Name, Vec<f64>), ParseError> {
        let weighted_tokens = lex_weighted(input)?;
        let weights: Vec<f64> = weighted_tokens.iter().map(|(_, _, w)| *w).collect();
        let tokens: Vec<(Token<'_>, Range)> = weighted_tokens
            .into_iter()
            .map(|(t, r, _)| (t, r))
            .collect();
        let mut pos = 0usize;
        let result = parse_Name(&tokens, &mut pos, 0)?;
        if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
            return Err(ParseError::TrailingTokens {
                found: format_token_friendly(&tokens[pos].0),
                range: tokens[pos].1,
                hint: Some(
                    Cow::Borrowed(
                        "the parser finished but input remains; check for missing operators or extra tokens",
                    ),
                ),
            });
        }
        Ok((result, weights))
    }
    /// B4: Parse with confidence scoring.
    ///
    /// Returns `(ast, confidence)` where `confidence` is the accumulated
    /// tropical weight of dispatch decisions along the parse path.
    ///
    /// **Interpretation:**
    /// - `0.0` — fully deterministic parse (no ambiguity encountered)
    /// - Low values (< 1.0) — mostly deterministic with minor ambiguity
    /// - High values (> 2.0) — significant ambiguity encountered
    ///
    /// Useful for language servers and IDE integration to flag low-confidence
    /// parses (e.g., display "ambiguous parse" diagnostics).
    pub fn parse_with_confidence(input: &str) -> Result<(Name, f64), ParseError> {
        let tokens = lex(input)?;
        let mut pos = 0usize;
        let result = parse_Name(&tokens, &mut pos, 0)?;
        if pos < tokens.len() && !matches!(tokens[pos].0, Token::Eof) {
            return Err(ParseError::TrailingTokens {
                found: format_token_friendly(&tokens[pos].0),
                range: tokens[pos].1,
                hint: Some(
                    Cow::Borrowed(
                        "the parser finished but input remains; check for missing operators or extra tokens",
                    ),
                ),
            });
        }
        let confidence = running_weight_Name();
        Ok((result, confidence))
    }
}
