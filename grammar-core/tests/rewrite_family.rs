use mettail_grammar_core::rewrite_family::*;
use proptest::prelude::*;

#[derive(Clone)]
enum Kind {
    Var(String),
    App(String),
    Bind(Vec<String>),
    Collection,
    Computation(Vec<String>),
}

#[derive(Clone)]
struct Node {
    kind: Kind,
    children: Vec<usize>,
}

enum Sort {
    Base,
    Arrow { domain: usize, body: usize },
    Collection(usize),
}

struct Constructor {
    name: String,
    domains: Vec<usize>,
    result: usize,
}

struct Fixture {
    nodes: Vec<Node>,
    sorts: Vec<Sort>,
    constructors: Vec<Constructor>,
    unknown_edges: std::collections::BTreeSet<(usize, usize)>,
}

impl Fixture {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            unknown_edges: std::collections::BTreeSet::new(),
            sorts: vec![
                Sort::Base,
                Sort::Arrow { domain: 0, body: 0 },
                Sort::Collection(0),
                Sort::Base,
            ],
            constructors: vec![
                Constructor {
                    name: "Lam".into(),
                    domains: vec![1],
                    result: 0,
                },
                Constructor {
                    name: "Pair".into(),
                    domains: vec![0, 0],
                    result: 0,
                },
                Constructor {
                    name: "Pack".into(),
                    domains: vec![2],
                    result: 0,
                },
            ],
        }
    }

    fn node(&mut self, kind: Kind, children: Vec<usize>) -> usize {
        let index = self.nodes.len();
        self.nodes.push(Node { kind, children });
        index
    }

    fn var(&mut self, name: &str) -> usize {
        self.node(Kind::Var(name.into()), vec![])
    }

    fn app(&mut self, name: &str, children: Vec<usize>) -> usize {
        self.node(Kind::App(name.into()), children)
    }

    fn projection(&mut self, selector: &str, family: &str, args: &[&str]) -> usize {
        let args = args.iter().map(|name| self.var(name)).collect();
        let call = self.app(family, args);
        self.app(selector, vec![call])
    }

    fn lambda(&mut self, binder: &str, body: usize) -> usize {
        let binding = self.node(Kind::Bind(vec![binder.into()]), vec![body]);
        self.app("Lam", vec![binding])
    }

    fn render_plan(&self, root: usize, side: RewriteSide, plan: &RewriteFamilyPlan) -> String {
        fn walk(
            f: &Fixture,
            id: usize,
            side: RewriteSide,
            plan: &RewriteFamilyPlan,
            next: &mut usize,
        ) -> String {
            let occurrence = *next;
            *next += 1;
            let children: Vec<_> = f.nodes[id]
                .children
                .iter()
                .map(|&child| walk(f, child, side, plan, next))
                .collect();
            if let Some(edit) = plan
                .replacements
                .iter()
                .find(|edit| edit.side == side && edit.occurrence == occurrence)
            {
                assert_eq!(edit.subtree_end, *next);
                let family = &plan.families[edit.family];
                return match side {
                    RewriteSide::Left => family.source.clone(),
                    RewriteSide::Right => family.target.clone(),
                };
            }
            match &f.nodes[id].kind {
                Kind::Var(name) => name.clone(),
                Kind::App(name) => format!(
                    "({name}{})",
                    children.iter().map(|x| format!(" {x}")).collect::<String>()
                ),
                Kind::Bind(names) => {
                    let names = names
                        .iter()
                        .enumerate()
                        .map(|(index, name)| {
                            plan.binder_renames
                                .iter()
                                .find(|edit| {
                                    edit.binder_index == index
                                        && match side {
                                            RewriteSide::Left => edit.left_occurrence,
                                            RewriteSide::Right => edit.right_occurrence,
                                        } == occurrence
                                })
                                .map(|edit| edit.name.as_str())
                                .unwrap_or(name)
                        })
                        .collect::<Vec<_>>();
                    format!("^[{}].{}", names.join(","), children[0])
                },
                Kind::Collection => format!("{{{}}}", children.join(",")),
                Kind::Computation(names) => {
                    format!("compute[{}]({})", names.join(","), children.join(","))
                },
            }
        }
        walk(self, root, side, plan, &mut 0)
    }
}

struct Reader<'a>(&'a Fixture);

impl<'a> RewriteFamilyReader for Reader<'a> {
    type Node = usize;
    type Name = &'a str;
    type Sort = usize;
    type Error = &'static str;

    fn kind(&self, node: usize) -> Result<RewritePatternKind<&'a str>, Self::Error> {
        Ok(match &self.0.nodes[node].kind {
            Kind::Var(name) => RewritePatternKind::Variable(name),
            Kind::App(name) => RewritePatternKind::Application(name),
            Kind::Bind(names) => RewritePatternKind::Abstraction { binders: names.len() },
            Kind::Collection => RewritePatternKind::Context,
            Kind::Computation(_) => RewritePatternKind::Computation,
        })
    }
    fn child_count(&self, node: usize) -> usize {
        self.0.nodes[node].children.len()
    }
    fn child_at(&self, node: usize, index: usize) -> Option<usize> {
        self.0.nodes[node].children.get(index).copied()
    }
    fn binder_at(&self, node: usize, index: usize) -> Option<&'a str> {
        match &self.0.nodes[node].kind {
            Kind::Bind(names) => names.get(index).map(String::as_str),
            _ => None,
        }
    }
    fn variable_count(&self, node: usize) -> usize {
        match &self.0.nodes[node].kind {
            Kind::Computation(names) => names.len(),
            _ => 0,
        }
    }
    fn variable_at(&self, node: usize, index: usize) -> Option<&'a str> {
        match &self.0.nodes[node].kind {
            Kind::Computation(names) => names.get(index).map(String::as_str),
            _ => None,
        }
    }
    fn same_header(&self, left: usize, right: usize) -> Result<bool, Self::Error> {
        Ok(match (&self.0.nodes[left].kind, &self.0.nodes[right].kind) {
            (Kind::Var(l), Kind::Var(r)) | (Kind::App(l), Kind::App(r)) => l == r,
            (Kind::Bind(l), Kind::Bind(r)) => l == r,
            (Kind::Collection, Kind::Collection) => true,
            (Kind::Computation(l), Kind::Computation(r)) => l == r,
            _ => false,
        })
    }
    fn same_name(&self, left: &'a str, right: &'a str) -> bool {
        left == right
    }
    fn name_is(&self, name: &'a str, spelling: &str) -> bool {
        name == spelling
    }
    fn same_sort(&self, left: usize, right: usize) -> bool {
        left == right
    }
    fn valid_sort(&self, sort: usize) -> Result<bool, Self::Error> {
        Ok(sort < self.0.sorts.len())
    }
    fn node_sort(
        &self,
        node: usize,
        expected: Option<usize>,
    ) -> Result<Option<usize>, Self::Error> {
        if let Kind::App(name) = &self.0.nodes[node].kind {
            let ctor = self
                .0
                .constructors
                .iter()
                .find(|ctor| ctor.name == *name)
                .ok_or("unknown constructor")?;
            if expected.is_some_and(|sort| sort != ctor.result)
                || self.child_count(node) != ctor.domains.len()
            {
                return Err("constructor signature mismatch");
            }
            Ok(Some(ctor.result))
        } else {
            Ok(expected)
        }
    }
    fn child_sort(
        &self,
        node: usize,
        expected: Option<usize>,
        index: usize,
    ) -> Result<Option<usize>, Self::Error> {
        if self.0.unknown_edges.contains(&(node, index)) {
            return Ok(None);
        }
        match &self.0.nodes[node].kind {
            Kind::App(name) => Ok(self
                .0
                .constructors
                .iter()
                .find(|ctor| ctor.name == *name)
                .ok_or("unknown constructor")?
                .domains
                .get(index)
                .copied()),
            Kind::Bind(_) => match expected.map(|sort| &self.0.sorts[sort]) {
                Some(Sort::Arrow { body, .. }) => Ok(Some(*body)),
                _ => Err("expected arrow"),
            },
            Kind::Collection => match expected.map(|sort| &self.0.sorts[sort]) {
                Some(Sort::Collection(element)) => Ok(Some(*element)),
                _ => Err("expected collection"),
            },
            _ => Err("no child sort"),
        }
    }
    fn abstraction_sorts(&self, expected: usize, _: usize) -> Result<(usize, usize), Self::Error> {
        match self.0.sorts[expected] {
            Sort::Arrow { domain, body } => Ok((domain, body)),
            _ => Err("expected arrow"),
        }
    }
}

fn family(
    name: &str,
    context_index: usize,
    domains: Vec<usize>,
) -> RewriteFamilyDeclaration<&str, usize> {
    RewriteFamilyDeclaration { context_index, name, domains, result: 0 }
}

fn problem(error: RewriteFamilyError<&str>) -> RewriteFamilyProblem {
    match error {
        RewriteFamilyError::Invalid { problem, .. } => problem,
        other => panic!("unexpected error: {other:?}"),
    }
}

proptest! {
    #[test]
    fn nested_contexts_preserve_each_binder_and_endpoint(depth in 0usize..20, seed in any::<u16>()) {
        let mut f = Fixture::new();
        let names: Vec<_> = (0..depth).map(|index| format!("v{seed}_{index}")).collect();
        let refs: Vec<_> = names.iter().map(String::as_str).collect();
        let mut left = f.projection("s", "step", &refs);
        let mut right = f.projection("t", "step", &refs);
        for name in names.iter().rev() {
            left = f.lambda(name, left);
            right = f.lambda(name, right);
        }
        let plan = plan_rewrite_families(&Reader(&f), left, right, &[family("step", 7, vec![0; depth])], &[], &[], &[]).unwrap();
        prop_assert!(plan.binder_renames.is_empty());
        prop_assert_eq!(plan.families[0].context_index, 7);
        let mut expected_left = plan.families[0].source.clone();
        let mut expected_right = plan.families[0].target.clone();
        for name in names.iter().rev() {
            expected_left = format!("(Lam ^[{name}].{expected_left})");
            expected_right = format!("(Lam ^[{name}].{expected_right})");
        }
        prop_assert_eq!(f.render_plan(left, RewriteSide::Left, &plan), expected_left);
        prop_assert_eq!(f.render_plan(right, RewriteSide::Right, &plan), expected_right);
    }

    #[test]
    fn declaration_order_is_independent_of_occurrence_order(reverse in any::<bool>(), count in 1usize..14) {
        let mut f = Fixture::new();
        let names: Vec<_> = (0..count).map(|index| format!("f{index}")).collect();
        let mut declarations: Vec<_> = names.iter().enumerate().map(|(index, name)| family(name, index + 3, vec![])).collect();
        if reverse { declarations.reverse(); }
        let left_children = names.iter().map(|name| f.projection("s", name, &[])).collect();
        let right_children = names.iter().map(|name| f.projection("t", name, &[])).collect();
        let lc = f.node(Kind::Collection, left_children);
        let rc = f.node(Kind::Collection, right_children);
        let left = f.app("Pack", vec![lc]);
        let right = f.app("Pack", vec![rc]);
        let plan = plan_rewrite_families(&Reader(&f), left, right, &declarations, &[], &[], &[]).unwrap();
        prop_assert_eq!(plan.families.iter().map(|x| x.context_index).collect::<Vec<_>>(), declarations.iter().map(|x| x.context_index).collect::<Vec<_>>());
        for side in [RewriteSide::Left, RewriteSide::Right] {
            let expected: Vec<_> = (0..count).map(|index| {
                let family = plan.families.iter().find(|x| x.context_index == index + 3).unwrap();
                match side { RewriteSide::Left => family.source.as_str(), RewriteSide::Right => family.target.as_str() }
            }).collect();
            let root = if side == RewriteSide::Left { left } else { right };
            prop_assert_eq!(f.render_plan(root, side, &plan), format!("(Pack {{{}}})", expected.join(",")));
        }
    }

    #[test]
    fn generated_names_avoid_all_reserved_sources(collisions in prop::collection::vec(0usize..80, 0..60)) {
        let mut f = Fixture::new();
        let l = f.projection("s", "step", &[]);
        let r = f.projection("t", "step", &[]);
        let names: Vec<_> = collisions.iter().map(|index| format!("__mettail_rewrite_{index}")).collect();
        let names: Vec<_> = names.iter().map(String::as_str).collect();
        let plan = plan_rewrite_families(&Reader(&f), l, r, &[family("step", 0, vec![])], &[], &names, &names).unwrap();
        prop_assert!(!names.contains(&plan.families[0].source.as_str()));
        prop_assert!(!names.contains(&plan.families[0].target.as_str()));
        prop_assert_ne!(&plan.families[0].source, &plan.families[0].target);
    }

    #[test]
    fn arbitrary_constructor_labels_and_categories_preserve_types(seed in any::<u16>(), padding in 0usize..20) {
        let mut f = Fixture::new();
        for _ in 0..padding { f.sorts.push(Sort::Base); }
        let result = f.sorts.len() - 1;
        let label = format!("Ctor_{seed}");
        f.constructors.push(Constructor { name: label.clone(), domains: vec![result], result });
        let left_hole = f.projection("s", "family", &[]);
        let right_hole = f.projection("t", "family", &[]);
        let left = f.app(&label, vec![left_hole]);
        let right = f.app(&label, vec![right_hole]);
        let declaration = RewriteFamilyDeclaration { name: "family", context_index: 0, domains: vec![], result };
        let plan = plan_rewrite_families(&Reader(&f), left, right, &[declaration], &[], &[], &[]).unwrap();
        prop_assert_eq!(f.render_plan(left, RewriteSide::Left, &plan), format!("({label} {})", plan.families[0].source));
    }
}

#[test]
fn legacy_rules_do_not_read_or_change_their_patterns() {
    let f = Fixture::new();
    let plan =
        plan_rewrite_families(&Reader(&f), usize::MAX, usize::MAX, &[], &[], &[], &[]).unwrap();
    assert_eq!(plan, RewriteFamilyPlan::default());
}

#[test]
fn sibling_binders_receive_distinct_names_without_renaming_unique_binders() {
    let mut f = Fixture::new();
    let mut sides = Vec::new();
    for selector in ["s", "t"] {
        let a = f.projection(selector, "a", &["x"]);
        let a = f.lambda("x", a);
        let b = f.projection(selector, "b", &["x"]);
        let b = f.lambda("x", b);
        sides.push(f.app("Pair", vec![a, b]));
    }
    let declarations = [family("a", 0, vec![0]), family("b", 1, vec![0])];
    let plan = plan_rewrite_families(&Reader(&f), sides[0], sides[1], &declarations, &[], &[], &[])
        .unwrap();
    assert_eq!(plan.binder_renames.len(), 2);
    assert_ne!(plan.binder_renames[0].name, plan.binder_renames[1].name);
    let generated: Vec<_> = plan
        .binder_renames
        .iter()
        .map(|x| x.name.as_str())
        .chain(
            plan.families
                .iter()
                .flat_map(|x| [x.source.as_str(), x.target.as_str()]),
        )
        .collect();
    let unique: std::collections::BTreeSet<_> = generated.iter().collect();
    assert_eq!(unique.len(), generated.len());
    for external in [&["x"][..], &[][..]] {
        let ambient = if external.is_empty() {
            vec![RewriteFamilyInput { name: "x", sort: 0, context_index: 8 }]
        } else {
            vec![]
        };
        let error = plan_rewrite_families(
            &Reader(&f),
            sides[0],
            sides[1],
            &declarations,
            &ambient,
            external,
            &[],
        )
        .unwrap_err();
        assert_eq!(
            problem(error),
            RewriteFamilyProblem::AmbiguousBinderReference { binder_index: 0 }
        );
    }
}

#[test]
fn unique_binder_keeps_context_and_premise_aliases() {
    let mut f = Fixture::new();
    let l = f.projection("s", "a", &["x"]);
    let r = f.projection("t", "a", &["x"]);
    let l = f.lambda("x", l);
    let r = f.lambda("x", r);
    let ambient = [RewriteFamilyInput { name: "x", sort: 0, context_index: 1 }];
    let plan =
        plan_rewrite_families(&Reader(&f), l, r, &[family("a", 0, vec![0])], &ambient, &["x"], &[])
            .unwrap();
    assert!(plan.binder_renames.is_empty());
}

#[test]
fn lexical_scope_restores_after_sibling_exit() {
    let mut f = Fixture::new();
    let mut sides = Vec::new();
    for selector in ["s", "t"] {
        let inner = f.projection(selector, "inside", &["x"]);
        let inner = f.lambda("x", inner);
        let outer = f.projection(selector, "outside", &["x"]);
        sides.push(f.app("Pair", vec![inner, outer]));
    }
    let declarations = [family("inside", 0, vec![0]), family("outside", 1, vec![3])];
    let ambient = [RewriteFamilyInput { name: "x", sort: 3, context_index: 2 }];
    let plan =
        plan_rewrite_families(&Reader(&f), sides[0], sides[1], &declarations, &ambient, &[], &[])
            .unwrap();
    assert_eq!(plan.families.len(), 2);
}

#[test]
fn scope_and_order_refusals_are_exact() {
    for (args, domains, expected) in [
        (vec![], vec![], RewriteFamilyProblem::MissingDependency),
        (vec!["escaped"], vec![0], RewriteFamilyProblem::EscapedArgument),
        (vec!["x"], vec![3], RewriteFamilyProblem::ArgumentSort),
        (vec!["x", "x"], vec![0, 0], RewriteFamilyProblem::RepeatedArgument),
        (vec!["x"], vec![], RewriteFamilyProblem::ArgumentArity),
    ] {
        let mut f = Fixture::new();
        let l = f.projection("s", "a", &args);
        let r = f.projection("t", "a", &args);
        let l = f.lambda("x", l);
        let r = f.lambda("x", r);
        let error =
            plan_rewrite_families(&Reader(&f), l, r, &[family("a", 0, domains)], &[], &[], &[])
                .unwrap_err();
        assert_eq!(problem(error), expected);
    }
    let mut f = Fixture::new();
    let l = f.projection("s", "a", &["x", "y"]);
    let r = f.projection("t", "a", &["y", "x"]);
    let inputs = [
        RewriteFamilyInput { name: "x", sort: 0, context_index: 1 },
        RewriteFamilyInput { name: "y", sort: 0, context_index: 2 },
    ];
    assert_eq!(
        problem(
            plan_rewrite_families(
                &Reader(&f),
                l,
                r,
                &[family("a", 0, vec![0, 0])],
                &inputs,
                &[],
                &[]
            )
            .unwrap_err()
        ),
        RewriteFamilyProblem::ProjectionMismatch
    );
}

#[test]
fn nearest_shadow_cannot_omit_an_outer_dependency() {
    let mut f = Fixture::new();
    let l = f.projection("s", "a", &["x"]);
    let r = f.projection("t", "a", &["x"]);
    let l = f.lambda("x", l);
    let r = f.lambda("x", r);
    let l = f.lambda("x", l);
    let r = f.lambda("x", r);
    assert_eq!(
        problem(
            plan_rewrite_families(&Reader(&f), l, r, &[family("a", 0, vec![0])], &[], &[], &[])
                .unwrap_err()
        ),
        RewriteFamilyProblem::MissingDependency
    );
}

#[test]
fn computational_contexts_expose_forbidden_holes_and_hidden_names() {
    let mut f = Fixture::new();
    let l = f.projection("s", "a", &[]);
    let r = f.projection("t", "a", &[]);
    let l = f.node(Kind::Computation(vec!["bound".into()]), vec![l]);
    let r = f.node(Kind::Computation(vec!["bound".into()]), vec![r]);
    let error = plan_rewrite_families(&Reader(&f), l, r, &[family("a", 0, vec![])], &[], &[], &[])
        .unwrap_err();
    assert!(
        matches!(error, RewriteFamilyError::Invalid { problem: RewriteFamilyProblem::ProjectionOutsideTypedContext, location: RewriteFamilyLocation::Pattern { path, .. }, .. } if path == vec![0])
    );

    let mut sides = Vec::new();
    for selector in ["s", "t"] {
        let hole = f.projection(selector, "a", &[]);
        let payload = f.var("ordinary");
        let payload = f.node(Kind::Computation(vec!["__mettail_rewrite_0".into()]), vec![payload]);
        sides.push(f.app("Pair", vec![hole, payload]));
    }
    let plan = plan_rewrite_families(
        &Reader(&f),
        sides[0],
        sides[1],
        &[family("a", 0, vec![])],
        &[],
        &[],
        &[],
    )
    .unwrap();
    assert_ne!(plan.families[0].source, "__mettail_rewrite_0");
    assert!(f
        .render_plan(sides[1], RewriteSide::Right, &plan)
        .contains("compute[__mettail_rewrite_0](ordinary)"));
}

#[test]
fn late_failure_does_not_publish_earlier_edits() {
    let mut f = Fixture::new();
    let mut sides = Vec::new();
    for selector in ["s", "t"] {
        let first = f.projection(selector, "a", &[]);
        let second = f.var(if selector == "s" { "before" } else { "after" });
        sides.push(f.app("Pair", vec![first, second]));
    }
    let before = f.render_plan(sides[0], RewriteSide::Left, &RewriteFamilyPlan::default());
    assert_eq!(
        problem(
            plan_rewrite_families(
                &Reader(&f),
                sides[0],
                sides[1],
                &[family("a", 0, vec![])],
                &[],
                &[],
                &[]
            )
            .unwrap_err()
        ),
        RewriteFamilyProblem::ContextMismatch
    );
    assert_eq!(
        f.render_plan(sides[0], RewriteSide::Left, &RewriteFamilyPlan::default()),
        before
    );
}

#[test]
fn roster_and_projection_polarity_are_checked() {
    let mut f = Fixture::new();
    let l = f.projection("s", "a", &[]);
    let r = f.projection("t", "a", &[]);
    let repeated_l = f.app("Pair", vec![l, l]);
    let repeated_r = f.app("Pair", vec![r, r]);
    assert_eq!(
        problem(
            plan_rewrite_families(
                &Reader(&f),
                repeated_l,
                repeated_r,
                &[family("a", 0, vec![])],
                &[],
                &[],
                &[]
            )
            .unwrap_err()
        ),
        RewriteFamilyProblem::RepeatedFamily
    );
    assert_eq!(
        problem(
            plan_rewrite_families(&Reader(&f), r, l, &[family("a", 0, vec![])], &[], &[], &[])
                .unwrap_err()
        ),
        RewriteFamilyProblem::ProjectionMismatch
    );
    assert_eq!(
        problem(
            plan_rewrite_families(
                &Reader(&f),
                l,
                r,
                &[family("a", 0, vec![]), family("b", 1, vec![])],
                &[],
                &[],
                &[]
            )
            .unwrap_err()
        ),
        RewriteFamilyProblem::MissingFamily
    );
    assert_eq!(
        problem(
            plan_rewrite_families(
                &Reader(&f),
                l,
                r,
                &[family("a", 0, vec![]), family("a", 1, vec![])],
                &[],
                &[],
                &[]
            )
            .unwrap_err()
        ),
        RewriteFamilyProblem::DuplicateDeclaration
    );
    assert_eq!(
        problem(
            plan_rewrite_families(&Reader(&f), l, r, &[family("a", 0, vec![99])], &[], &[], &[])
                .unwrap_err()
        ),
        RewriteFamilyProblem::UnknownSort
    );
    let raw = f.var("a");
    assert_eq!(
        problem(
            plan_rewrite_families(&Reader(&f), raw, raw, &[family("a", 0, vec![])], &[], &[], &[])
                .unwrap_err()
        ),
        RewriteFamilyProblem::FamilyAsValue
    );
}

proptest! {
    #[test]
    fn unknown_sort_edges_disable_every_descendant(above in 0usize..14, below in 0usize..14) {
        let mut f = Fixture::new();
        f.constructors.push(Constructor { name: "Nest".into(), domains: vec![0], result: 0 });
        let mut roots = Vec::new();
        for selector in ["s", "t"] {
            let mut node = f.projection(selector, "a", &[]);
            for _ in 0..below { node = f.app("Nest", vec![node]); }
            node = f.app("Nest", vec![node]);
            f.unknown_edges.insert((node, 0));
            for _ in 0..above { node = f.app("Nest", vec![node]); }
            roots.push(node);
        }
        let error = plan_rewrite_families(&Reader(&f), roots[0], roots[1], &[family("a", 0, vec![])], &[], &[], &[]).unwrap_err();
        match error {
            RewriteFamilyError::Invalid { problem: RewriteFamilyProblem::ProjectionOutsideTypedContext, location: RewriteFamilyLocation::Pattern { path, .. }, .. } => {
                prop_assert_eq!(path, vec![0; above + below + 1]);
            },
            other => prop_assert!(false, "unexpected error: {other:?}"),
        }
    }

    #[test]
    fn unknown_sibling_preserves_typed_holes_and_name_census(unknown_first in any::<bool>(), depth in 0usize..16) {
        let mut f = Fixture::new();
        f.constructors.push(Constructor { name: "Nest".into(), domains: vec![0], result: 0 });
        let mut roots = Vec::new();
        for selector in ["s", "t"] {
            let hole = f.projection(selector, "a", &[]);
            let mut unknown = f.var("__mettail_rewrite_0");
            for _ in 0..depth { unknown = f.app("Nest", vec![unknown]); }
            let children = if unknown_first { vec![unknown, hole] } else { vec![hole, unknown] };
            let root = f.app("Pair", children);
            f.unknown_edges.insert((root, if unknown_first { 0 } else { 1 }));
            roots.push(root);
        }
        let plan = plan_rewrite_families(&Reader(&f), roots[0], roots[1], &[family("a", 0, vec![])], &[], &[], &[]).unwrap();
        prop_assert_ne!(&plan.families[0].source, "__mettail_rewrite_0");
        prop_assert_ne!(&plan.families[0].target, "__mettail_rewrite_0");
        let mut unknown = "__mettail_rewrite_0".to_string();
        for _ in 0..depth { unknown = format!("(Nest {unknown})"); }
        let endpoint = &plan.families[0].target;
        let expected = if unknown_first { format!("(Pair {unknown} {endpoint})") } else { format!("(Pair {endpoint} {unknown})") };
        prop_assert_eq!(f.render_plan(roots[1], RewriteSide::Right, &plan), expected);
    }
}

#[test]
fn missing_and_present_child_sort_disagreement_is_refused() {
    let mut f = Fixture::new();
    let l = f.projection("s", "a", &[]);
    let r = f.projection("t", "a", &[]);
    let ordinary = f.var("v");
    let l = f.app("Pair", vec![l, ordinary]);
    let r = f.app("Pair", vec![r, ordinary]);
    f.unknown_edges.insert((l, 0));
    let error = plan_rewrite_families(&Reader(&f), l, r, &[family("a", 0, vec![])], &[], &[], &[])
        .unwrap_err();
    assert!(
        matches!(error, RewriteFamilyError::Invalid { problem: RewriteFamilyProblem::ContextMismatch, location: RewriteFamilyLocation::Pattern { path, .. }, .. } if path == vec![0])
    );
}
