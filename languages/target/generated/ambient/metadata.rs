/// Static metadata for the #name language
pub struct AmbientMetadata;
impl mettail_runtime::LanguageMetadata for AmbientMetadata {
    fn name(&self) -> &'static str {
        "Ambient"
    }
    fn types(&self) -> &'static [mettail_runtime::TypeDef] {
        &[
            mettail_runtime::TypeDef {
                name: "Proc",
                native_type: None,
                is_primary: true,
            },
            mettail_runtime::TypeDef {
                name: "Name",
                native_type: None,
                is_primary: false,
            },
        ]
    }
    fn terms(&self) -> &'static [mettail_runtime::TermDef] {
        &[
            mettail_runtime::TermDef {
                name: "PZero",
                type_name: "Proc",
                syntax: "0",
                description: None,
                fields: &[],
            },
            mettail_runtime::TermDef {
                name: "PIn",
                type_name: "Proc",
                syntax: "in(name,proc)",
                description: None,
                fields: &[
                    mettail_runtime::FieldDef {
                        name: "f1",
                        ty: "Name",
                        is_binder: false,
                    },
                    mettail_runtime::FieldDef {
                        name: "f3",
                        ty: "Proc",
                        is_binder: false,
                    },
                ],
            },
            mettail_runtime::TermDef {
                name: "POut",
                type_name: "Proc",
                syntax: "out(name,proc)",
                description: None,
                fields: &[
                    mettail_runtime::FieldDef {
                        name: "f1",
                        ty: "Name",
                        is_binder: false,
                    },
                    mettail_runtime::FieldDef {
                        name: "f3",
                        ty: "Proc",
                        is_binder: false,
                    },
                ],
            },
            mettail_runtime::TermDef {
                name: "POpen",
                type_name: "Proc",
                syntax: "open(name,proc)",
                description: None,
                fields: &[
                    mettail_runtime::FieldDef {
                        name: "f1",
                        ty: "Name",
                        is_binder: false,
                    },
                    mettail_runtime::FieldDef {
                        name: "f3",
                        ty: "Proc",
                        is_binder: false,
                    },
                ],
            },
            mettail_runtime::TermDef {
                name: "PAmb",
                type_name: "Proc",
                syntax: "name[proc]",
                description: None,
                fields: &[
                    mettail_runtime::FieldDef {
                        name: "f0",
                        ty: "Name",
                        is_binder: false,
                    },
                    mettail_runtime::FieldDef {
                        name: "f2",
                        ty: "Proc",
                        is_binder: false,
                    },
                ],
            },
            mettail_runtime::TermDef {
                name: "PNew",
                type_name: "Proc",
                syntax: "new(x,p)",
                description: None,
                fields: &[
                    mettail_runtime::FieldDef {
                        name: "^x.p",
                        ty: "[Name -> Proc]",
                        is_binder: true,
                    },
                ],
            },
            mettail_runtime::TermDef {
                name: "PPar",
                type_name: "Proc",
                syntax: "{ proc ... }",
                description: None,
                fields: &[
                    mettail_runtime::FieldDef {
                        name: "f0",
                        ty: "HashBag(Proc)",
                        is_binder: false,
                    },
                ],
            },
        ]
    }
    fn equations(&self) -> &'static [mettail_runtime::EquationDef] {
        &[
            mettail_runtime::EquationDef {
                conditions: &[],
                lhs: "new(x,new(y,P))",
                rhs: "new(y,new(x,P))",
                is_guarded: false,
            },
            mettail_runtime::EquationDef {
                conditions: &["x # ...rest"],
                lhs: "{{new(x,P) | ...rest}}",
                rhs: "new(x,{{P | ...rest}})",
                is_guarded: false,
            },
            mettail_runtime::EquationDef {
                conditions: &["x # P"],
                lhs: "in(N,new(x,P))",
                rhs: "new(x,in(N,P))",
                is_guarded: false,
            },
            mettail_runtime::EquationDef {
                conditions: &["x # P"],
                lhs: "out(N,new(x,P))",
                rhs: "new(x,out(N,P))",
                is_guarded: false,
            },
            mettail_runtime::EquationDef {
                conditions: &["x # P"],
                lhs: "open(N,new(x,P))",
                rhs: "new(x,open(N,P))",
                is_guarded: false,
            },
            mettail_runtime::EquationDef {
                conditions: &["x # P"],
                lhs: "N[new(x,P)]",
                rhs: "new(x,N[P])",
                is_guarded: false,
            },
        ]
    }
    fn rewrites(&self) -> &'static [mettail_runtime::RewriteDef] {
        &[
            mettail_runtime::RewriteDef {
                name: Some("InRule"),
                conditions: &[],
                premise: None,
                lhs: "{{N[{{in(M,P) | ...rest1}}] | M[R] | ...rest2}}",
                rhs: "{{M[{{N[{{P | ...rest1}}] | R}}] | ...rest2}}",
                is_guarded: false,
            },
            mettail_runtime::RewriteDef {
                name: Some("OutRule"),
                conditions: &[],
                premise: None,
                lhs: "M[{{N[{{out(M,P) | ...rest1}}] | R | ...rest2}}]",
                rhs: "{{N[{{P | ...rest1}}] | M[R] | ...rest2}}",
                is_guarded: false,
            },
            mettail_runtime::RewriteDef {
                name: Some("OpenRule"),
                conditions: &[],
                premise: None,
                lhs: "{{open(N,P) | N[Q] | ...rest}}",
                rhs: "{{P | Q | ...rest}}",
                is_guarded: false,
            },
            mettail_runtime::RewriteDef {
                name: Some("ParCong"),
                conditions: &["S ~> T"],
                premise: Some(("S", "T")),
                lhs: "{{S | ...rest}}",
                rhs: "{{T | ...rest}}",
                is_guarded: false,
            },
            mettail_runtime::RewriteDef {
                name: Some("NewCong"),
                conditions: &["S ~> T"],
                premise: Some(("S", "T")),
                lhs: "new(x,S)",
                rhs: "new(x,T)",
                is_guarded: false,
            },
            mettail_runtime::RewriteDef {
                name: Some("AmbCong"),
                conditions: &["S ~> T"],
                premise: Some(("S", "T")),
                lhs: "N[S]",
                rhs: "N[T]",
                is_guarded: false,
            },
        ]
    }
    fn logic_relations(&self) -> &'static [mettail_runtime::LogicRelationDef] {
        &[]
    }
    fn logic_rules(&self) -> &'static [mettail_runtime::LogicRuleDef] {
        &[]
    }
    fn builtin_predicates(&self) -> &'static [mettail_runtime::BuiltinPredicateDef] {
        &[]
    }
    fn theories(&self) -> &'static [mettail_runtime::TheoryDef] {
        &[]
    }
    fn channels(&self) -> &'static [mettail_runtime::ChannelDef] {
        &[]
    }
    fn join_patterns(&self) -> &'static [mettail_runtime::JoinPatternDef] {
        &[]
    }
    fn connectives(&self) -> &'static [mettail_runtime::ConnectiveDef] {
        &[]
    }
}
