//! Bounded recursive specification for the constructor-emission PDA.
//!
//! The functions in this file are deliberately recursive and must only be
//! used by the shallow equivalence tests below. Keeping the oracle under
//! `tests/` separates it physically from production sources while the path
//! module lets it inspect the emitter's private primitives.

use super::*;

fn emit_category_recursive(
    schema: &Schema,
    category: &str,
    node: &DebugNode,
) -> Result<String, EmitError> {
    let (head, args): (&str, &[DebugNode]) = match node {
        DebugNode::Call { head, args } => (head.as_str(), args.as_slice()),
        DebugNode::Ident(head) => (head.as_str(), &[]),
        other => {
            return Err(EmitError::ShapeMismatch {
                expected: format!("a constructor of `{category}`"),
                found: describe(other),
            })
        },
    };

    let variant = match schema
        .variants
        .get(&(category.to_string(), head.to_string()))
    {
        Some(variant) => variant,
        None => {
            let elsewhere = schema.categories_declaring(head);
            return Err(if elsewhere.is_empty() {
                EmitError::UnknownConstructor { label: head.to_string() }
            } else {
                EmitError::WrongCategory {
                    label: head.to_string(),
                    expected: category.to_string(),
                    found_in: elsewhere.into_iter().map(str::to_string).collect(),
                }
            });
        },
    };

    if variant.kind == "literal" || variant.kind == "collit" {
        let native = schema
            .natives
            .get(category)
            .cloned()
            .flatten()
            .unwrap_or_else(|| "-".to_string());
        let payload = args.first().ok_or_else(|| EmitError::ShapeMismatch {
            expected: format!("`{head}(<{native}>)`"),
            found: "a nullary constructor".to_string(),
        })?;
        let inner = if variant.kind == "collit" {
            match variant.fields.first() {
                Some(FieldSpec::CollLit { kind, elem }) => {
                    emit_collection_recursive(schema, kind, elem, payload, true)?
                },
                _ => emit_native(&native, payload)?,
            }
        } else {
            emit_native(&native, payload)?
        };
        return Ok(format!("{category}::{head}({inner})"));
    }

    if variant.fields.is_empty() {
        if !args.is_empty() {
            return Err(EmitError::ShapeMismatch {
                expected: format!("`{head}` with no arguments"),
                found: format!("{} argument(s)", args.len()),
            });
        }
        return Ok(format!("{category}::{head}"));
    }

    if args.len() != variant.fields.len() {
        return Err(EmitError::ShapeMismatch {
            expected: format!("`{head}` with {} argument(s)", variant.fields.len()),
            found: format!("{} argument(s)", args.len()),
        });
    }

    let mut rendered = Vec::with_capacity(variant.fields.len());
    for (spec, argument) in variant.fields.iter().zip(args) {
        rendered.push(emit_field_recursive(schema, spec, argument)?);
    }
    Ok(format!("{category}::{head}({})", rendered.join(", ")))
}

fn emit_field_recursive(
    schema: &Schema,
    spec: &FieldSpec,
    node: &DebugNode,
) -> Result<String, EmitError> {
    match spec {
        FieldSpec::Opt(inner) => match node {
            DebugNode::Ident(name) if name == "None" => Ok("None".to_string()),
            DebugNode::Call { head, args } if head == "Some" && args.len() == 1 => {
                Ok(format!("Some({})", emit_field_recursive(schema, inner, &args[0])?))
            },
            other => Err(EmitError::ShapeMismatch {
                expected: "`Some(..)` or `None`".to_string(),
                found: describe(other),
            }),
        },
        FieldSpec::Cat(category) => Ok(format!(
            "std::sync::Arc::new({})",
            emit_category_recursive(schema, category, node)?
        )),
        FieldSpec::Var => emit_ordvar(node),
        FieldSpec::Native(native) => emit_native(native, node),
        FieldSpec::Coll { kind, elem } => {
            emit_collection_recursive(schema, kind, elem, node, false)
        },
        FieldSpec::CollLit { kind, elem } => {
            emit_collection_recursive(schema, kind, elem, node, true)
        },
        FieldSpec::NativeZipper { storage, access, key, value } => {
            let constructor = match access {
                ZipperAccess::Read => "ReadZipperLit",
                ZipperAccess::Write => "WriteZipperLit",
            };
            let DebugNode::Call { head, args } = node else {
                return Err(EmitError::ShapeMismatch {
                    expected: format!("`{constructor}(PathMapLit, [u8])`"),
                    found: describe(node),
                });
            };
            if head != constructor || args.len() != 2 {
                return Err(EmitError::ShapeMismatch {
                    expected: format!("`{constructor}(PathMapLit, [u8])`"),
                    found: describe(node),
                });
            }
            let pathmap = emit_pathmap_recursive(schema, key, value, &args[0])?;
            let focus = emit_byte_vector_recursive(&args[1])?;
            let payload = format!("mettail_runtime::{constructor}({pathmap}, {focus})");
            Ok(match storage {
                ZipperStorage::Direct => payload,
                ZipperStorage::Arc => format!("std::sync::Arc::new({payload})"),
            })
        },
        FieldSpec::Scope1 { body, .. } => match node {
            DebugNode::Struct { head, fields } if head == "Scope" => {
                let pattern = field_named(fields, "pattern")?;
                let body_node = field_named(fields, "body")?;
                Ok(format!(
                    "mettail_runtime::Scope::from_parts_unsafe({}, std::sync::Arc::new({}))",
                    emit_binder(pattern)?,
                    emit_category_recursive(schema, body, body_node)?
                ))
            },
            other => Err(EmitError::ShapeMismatch {
                expected: "`Scope { pattern: .., body: .. }`".to_string(),
                found: describe(other),
            }),
        },
        FieldSpec::ScopeN { body, .. } => match node {
            DebugNode::Struct { head, fields } if head == "Scope" => {
                let pattern = field_named(fields, "pattern")?;
                let body_node = field_named(fields, "body")?;
                let binders = match pattern {
                    DebugNode::List(items) => items
                        .iter()
                        .map(emit_binder)
                        .collect::<Result<Vec<_>, _>>()?,
                    other => {
                        return Err(EmitError::ShapeMismatch {
                            expected: "a `[Binder(..), ..]` multi-binder pattern".to_string(),
                            found: describe(other),
                        })
                    },
                };
                Ok(format!(
                    "mettail_runtime::Scope::from_parts_unsafe(vec![{}], std::sync::Arc::new({}))",
                    binders.join(", "),
                    emit_category_recursive(schema, body, body_node)?
                ))
            },
            other => Err(EmitError::ShapeMismatch {
                expected: "`Scope { pattern: [..], body: .. }`".to_string(),
                found: describe(other),
            }),
        },
        FieldSpec::OpaqueToken => match node {
            DebugNode::Str(text) => Ok(format!("std::string::String::from({})", quote_rust(text))),
            other => Err(EmitError::ShapeMismatch {
                expected: "a token-text string literal".to_string(),
                found: describe(other),
            }),
        },
        FieldSpec::Pred => Err(EmitError::UnsupportedFieldType {
            descriptor: "pred (BehavioralPred)".to_string(),
        }),
        FieldSpec::OpaqueGuest => Err(EmitError::UnsupportedFieldType {
            descriptor: "opaque:guest (Arc<FltNode>)".to_string(),
        }),
    }
}

fn emit_byte_vector_recursive(node: &DebugNode) -> Result<String, EmitError> {
    let DebugNode::List(bytes) = node else {
        return Err(EmitError::ShapeMismatch {
            expected: "a `[u8, ..]` focus vector".to_string(),
            found: describe(node),
        });
    };
    let mut rendered = Vec::with_capacity(bytes.len());
    for byte in bytes {
        let DebugNode::Int(byte) = byte else {
            return Err(EmitError::ShapeMismatch {
                expected: "a byte integer in `0..=255`".to_string(),
                found: describe(byte),
            });
        };
        let byte = u8::try_from(*byte).map_err(|_| EmitError::ShapeMismatch {
            expected: "a byte integer in `0..=255`".to_string(),
            found: byte.to_string(),
        })?;
        rendered.push(format!("{byte}_u8"));
    }
    Ok(format!("vec![{}]", rendered.join(", ")))
}

fn emit_pathmap_recursive(
    schema: &Schema,
    key_category: &str,
    value_category: &str,
    node: &DebugNode,
) -> Result<String, EmitError> {
    match node {
        DebugNode::Ident(mode) if mode == "Empty" => {
            Ok("mettail_runtime::PathMapLit::Empty".to_string())
        },
        DebugNode::Call { head: mode, args } if args.len() == 1 && mode == "Set" => {
            let inner = unwrap_lit_container(&args[0], "HashMapLit");
            let entries = match inner {
                DebugNode::Map(entries) => entries.as_slice(),
                DebugNode::Set(items) if items.is_empty() => &[],
                other => {
                    return Err(EmitError::ShapeMismatch {
                        expected: "`Set(HashMapLit({key: (), ..}))`".to_string(),
                        found: describe(other),
                    })
                },
            };
            let mut pairs = Vec::with_capacity(entries.len());
            for (key, unit) in entries {
                if !matches!(unit, DebugNode::Tuple(items) if items.is_empty()) {
                    return Err(EmitError::ShapeMismatch {
                        expected: "the unit marker `()` for set-mode path membership".to_string(),
                        found: describe(unit),
                    });
                }
                pairs
                    .push(
                        format!("({}, ())", emit_category_recursive(schema, key_category, key)?,),
                    );
            }
            Ok(format!(
                "mettail_runtime::PathMapLit::Set(mettail_runtime::HashMapLit::from_iter(vec![{}]))",
                pairs.join(", "),
            ))
        },
        DebugNode::Call { head: mode, args } if args.len() == 1 && mode == "Map" => {
            let inner = unwrap_lit_container(&args[0], "HashMapLit");
            let entries = match inner {
                DebugNode::Map(entries) => entries.as_slice(),
                DebugNode::Set(items) if items.is_empty() => &[],
                other => {
                    return Err(EmitError::ShapeMismatch {
                        expected: "`Map(HashMapLit({key: value, ..}))`".to_string(),
                        found: describe(other),
                    })
                },
            };
            let mut pairs = Vec::with_capacity(entries.len());
            for (key, value) in entries {
                pairs.push(format!(
                    "({}, {})",
                    emit_category_recursive(schema, key_category, key)?,
                    emit_category_recursive(schema, value_category, value)?,
                ));
            }
            Ok(format!(
                "mettail_runtime::PathMapLit::Map(mettail_runtime::HashMapLit::from_iter(vec![{}]))",
                pairs.join(", "),
            ))
        },
        other => Err(EmitError::ShapeMismatch {
            expected: "`Empty`, `Set(HashMapLit(..))`, or `Map(HashMapLit(..))`".to_string(),
            found: describe(other),
        }),
    }
}

fn emit_collection_recursive(
    schema: &Schema,
    kind: &str,
    elem: &str,
    node: &DebugNode,
    is_literal: bool,
) -> Result<String, EmitError> {
    match kind {
        "HashBag" => match node {
            DebugNode::Struct { head, fields } if head == "HashBag" => {
                let counts = field_named(fields, "counts")?;
                let entries = match counts {
                    DebugNode::Map(entries) => entries.as_slice(),
                    DebugNode::Set(items) if items.is_empty() => &[],
                    other => {
                        return Err(EmitError::ShapeMismatch {
                            expected: "`counts: {elem: n, ..}`".to_string(),
                            found: describe(other),
                        })
                    },
                };
                let mut parts = Vec::with_capacity(entries.len());
                for (key, count) in entries {
                    let repeats = match count {
                        DebugNode::Int(count) if *count >= 0 => *count as usize,
                        other => {
                            return Err(EmitError::ShapeMismatch {
                                expected: "a non-negative multiplicity".to_string(),
                                found: describe(other),
                            })
                        },
                    };
                    let rendered = emit_category_recursive(schema, elem, key)?;
                    for _ in 0..repeats {
                        parts.push(rendered.clone());
                    }
                }
                Ok(format!("mettail_runtime::HashBag::from_iter(vec![{}])", parts.join(", ")))
            },
            other => Err(EmitError::ShapeMismatch {
                expected: "`HashBag { counts: .., total_count: .. }`".to_string(),
                found: describe(other),
            }),
        },
        "Vec" => match node {
            DebugNode::List(items) => {
                let mut parts = Vec::with_capacity(items.len());
                for item in items {
                    parts.push(emit_category_recursive(schema, elem, item)?);
                }
                Ok(format!("vec![{}]", parts.join(", ")))
            },
            other => Err(EmitError::ShapeMismatch {
                expected: "a `[..]` list".to_string(),
                found: describe(other),
            }),
        },
        "HashSet" => {
            let inner = unwrap_lit_container(node, "HashSetLit");
            let items = match inner {
                DebugNode::Set(items) | DebugNode::List(items) => items.as_slice(),
                DebugNode::Map(entries) if entries.is_empty() => &[],
                other => {
                    return Err(EmitError::ShapeMismatch {
                        expected: "a `{..}` set".to_string(),
                        found: describe(other),
                    })
                },
            };
            let mut parts = Vec::with_capacity(items.len());
            for item in items {
                parts.push(emit_category_recursive(schema, elem, item)?);
            }
            let constructor = if is_literal {
                "mettail_runtime::HashSetLit::from_iter"
            } else {
                "std::collections::HashSet::from_iter"
            };
            Ok(format!("{constructor}(vec![{}])", parts.join(", ")))
        },
        "HashMap" => {
            let inner = unwrap_lit_container(node, "HashMapLit");
            let entries = match inner {
                DebugNode::Map(entries) => entries.as_slice(),
                DebugNode::Set(items) if items.is_empty() => &[],
                other => {
                    return Err(EmitError::ShapeMismatch {
                        expected: "a `{k: v, ..}` map".to_string(),
                        found: describe(other),
                    })
                },
            };
            let mut parts = Vec::with_capacity(entries.len());
            for (key, value) in entries {
                parts.push(format!(
                    "({}, {})",
                    emit_category_recursive(schema, elem, key)?,
                    emit_category_recursive(schema, elem, value)?
                ));
            }
            Ok(format!("mettail_runtime::HashMapLit::from_iter(vec![{}])", parts.join(", ")))
        },
        "PathMap" => emit_pathmap_recursive(schema, elem, elem, node),
        other => Err(EmitError::UnsupportedFieldType {
            descriptor: format!("collection kind `{other}`"),
        }),
    }
}

fn variant(category: &str, label: &str, fields: Vec<FieldSpec>) -> Variant {
    variant_with_kind(category, label, "normal", fields)
}

fn variant_with_kind(category: &str, label: &str, kind: &str, fields: Vec<FieldSpec>) -> Variant {
    Variant {
        category: category.to_string(),
        label: label.to_string(),
        kind: kind.to_string(),
        fields,
    }
}

fn recursive_schema() -> Schema {
    let mut schema = Schema {
        language: "EmitterPdaTest".to_string(),
        ..Schema::default()
    };
    schema.natives.insert("Term".to_string(), None);
    schema
        .natives
        .insert("Atom".to_string(), Some("i64".to_string()));
    schema
        .natives
        .insert("Bytes".to_string(), Some("Vec<u8>".to_string()));
    schema.natives.insert("SetExpr".to_string(), None);
    for variant in [
        variant("Term", "Leaf", Vec::new()),
        variant("Term", "Wrap", vec![FieldSpec::Cat("Term".to_string())]),
        variant(
            "Term",
            "Maybe",
            vec![FieldSpec::Opt(Box::new(FieldSpec::Cat("Term".to_string())))],
        ),
        variant(
            "Term",
            "Terms",
            vec![FieldSpec::Coll {
                kind: "Vec".to_string(),
                elem: "Term".to_string(),
            }],
        ),
        variant(
            "Term",
            "Bag",
            vec![FieldSpec::Coll {
                kind: "HashBag".to_string(),
                elem: "Term".to_string(),
            }],
        ),
        variant(
            "Term",
            "Map",
            vec![FieldSpec::Coll {
                kind: "HashMap".to_string(),
                elem: "Term".to_string(),
            }],
        ),
        variant(
            "Term",
            "Set",
            vec![FieldSpec::Coll {
                kind: "HashSet".to_string(),
                elem: "Term".to_string(),
            }],
        ),
        variant(
            "Term",
            "Path",
            vec![FieldSpec::Coll {
                kind: "PathMap".to_string(),
                elem: "Term".to_string(),
            }],
        ),
        variant("Term", "Text", vec![FieldSpec::Native("str".to_string())]),
        variant("Term", "Named", vec![FieldSpec::Var]),
        variant(
            "Term",
            "Scoped",
            vec![FieldSpec::Scope1 {
                binder: "String".to_string(),
                body: "Term".to_string(),
            }],
        ),
        variant(
            "Term",
            "ScopedMany",
            vec![FieldSpec::ScopeN {
                binder: "String".to_string(),
                body: "Term".to_string(),
            }],
        ),
        variant("Term", "Token", vec![FieldSpec::OpaqueToken]),
        variant("Term", "UnsupportedPred", vec![FieldSpec::Pred]),
        variant("Term", "UnsupportedGuest", vec![FieldSpec::OpaqueGuest]),
        variant_with_kind("Atom", "IntLit", "literal", Vec::new()),
        variant_with_kind("Bytes", "BytesLit", "literal", Vec::new()),
        variant_with_kind(
            "SetExpr",
            "SetLit",
            "collit",
            vec![FieldSpec::CollLit {
                kind: "HashSet".to_string(),
                elem: "Term".to_string(),
            }],
        ),
    ] {
        schema
            .variants
            .insert((variant.category.clone(), variant.label.clone()), variant);
    }
    schema
}

fn call(head: &str, args: Vec<DebugNode>) -> DebugNode {
    DebugNode::Call { head: head.to_string(), args }
}

fn free_var(name: &str) -> DebugNode {
    DebugNode::Struct {
        head: "FreeVar".to_string(),
        fields: vec![(
            "pretty_name".to_string(),
            call("Some", vec![DebugNode::Str(name.to_string())]),
        )],
    }
}

#[test]
fn constructor_emitter_matches_the_recursive_specification() {
    let schema = recursive_schema();
    let leaf = || DebugNode::Ident("Leaf".to_string());
    let fixtures = vec![
        ("Term", leaf()),
        ("Term", call("Wrap", vec![leaf()])),
        ("Term", call("Maybe", vec![call("Some", vec![call("Wrap", vec![leaf()])])])),
        ("Term", call("Maybe", vec![DebugNode::Ident("None".to_string())])),
        (
            "Term",
            call("Terms", vec![DebugNode::List(vec![leaf(), call("Wrap", vec![leaf()])])]),
        ),
        (
            "Term",
            call(
                "Bag",
                vec![DebugNode::Struct {
                    head: "HashBag".to_string(),
                    fields: vec![
                        (
                            "counts".to_string(),
                            DebugNode::Map(vec![
                                (call("Wrap", vec![leaf()]), DebugNode::Int(2)),
                                (leaf(), DebugNode::Int(1)),
                            ]),
                        ),
                        ("total_count".to_string(), DebugNode::Int(3)),
                    ],
                }],
            ),
        ),
        (
            "Term",
            call(
                "Map",
                vec![call(
                    "HashMapLit",
                    vec![DebugNode::Map(vec![
                        (leaf(), call("Wrap", vec![leaf()])),
                        (call("Wrap", vec![leaf()]), leaf()),
                    ])],
                )],
            ),
        ),
        (
            "Term",
            call(
                "Set",
                vec![call(
                    "HashSetLit",
                    vec![DebugNode::Set(vec![leaf(), call("Wrap", vec![leaf()])])],
                )],
            ),
        ),
        ("Term", call("Path", vec![DebugNode::Ident("Empty".to_string())])),
        (
            "Term",
            call(
                "Path",
                vec![call(
                    "Set",
                    vec![call(
                        "HashMapLit",
                        vec![DebugNode::Map(vec![
                            (leaf(), DebugNode::Tuple(Vec::new())),
                            (call("Wrap", vec![leaf()]), DebugNode::Tuple(Vec::new())),
                        ])],
                    )],
                )],
            ),
        ),
        (
            "Term",
            call(
                "Path",
                vec![call(
                    "Map",
                    vec![call(
                        "HashMapLit",
                        vec![DebugNode::Map(vec![(leaf(), call("Wrap", vec![leaf()]))])],
                    )],
                )],
            ),
        ),
        ("Term", call("Text", vec![DebugNode::Str("a\\n\\\"b".to_string())])),
        (
            "Term",
            call("Named", vec![call("OrdVar", vec![call("Free", vec![free_var("x")])])]),
        ),
        (
            "Term",
            call(
                "Scoped",
                vec![DebugNode::Struct {
                    head: "Scope".to_string(),
                    fields: vec![
                        ("pattern".to_string(), call("Binder", vec![free_var("x")])),
                        ("body".to_string(), call("Wrap", vec![leaf()])),
                    ],
                }],
            ),
        ),
        (
            "Term",
            call(
                "ScopedMany",
                vec![DebugNode::Struct {
                    head: "Scope".to_string(),
                    fields: vec![
                        (
                            "pattern".to_string(),
                            DebugNode::List(vec![
                                call("Binder", vec![free_var("x")]),
                                call("Binder", vec![free_var("y")]),
                            ]),
                        ),
                        ("body".to_string(), leaf()),
                    ],
                }],
            ),
        ),
        ("Term", call("Token", vec![DebugNode::Str("token".to_string())])),
        ("Atom", call("IntLit", vec![DebugNode::Int(42)])),
        (
            "Bytes",
            call("BytesLit", vec![DebugNode::List(vec![DebugNode::Int(0), DebugNode::Int(255)])]),
        ),
        (
            "SetExpr",
            call("SetLit", vec![call("HashSetLit", vec![DebugNode::Set(vec![leaf()])])]),
        ),
        ("Term", call("UnsupportedPred", vec![leaf()])),
        ("Term", call("UnsupportedGuest", vec![leaf()])),
        ("Term", call("Missing", Vec::new())),
        ("Term", call("Wrap", Vec::new())),
        ("Term", call("IntLit", vec![DebugNode::Int(42)])),
    ];

    for (category, fixture) in fixtures {
        assert_eq!(
            emit_category(&schema, category, &fixture),
            emit_category_recursive(&schema, category, &fixture),
            "iterative and recursive emitters diverged on {fixture:?}"
        );
    }
}

#[test]
fn constructor_emitter_rejects_unrepresentable_hashbag_multiplicity() {
    let schema = recursive_schema();
    let fixture = call(
        "Bag",
        vec![DebugNode::Struct {
            head: "HashBag".to_string(),
            fields: vec![
                (
                    "counts".to_string(),
                    DebugNode::Map(vec![(
                        DebugNode::Ident("Leaf".to_string()),
                        DebugNode::Int(i128::MAX),
                    )]),
                ),
                ("total_count".to_string(), DebugNode::Int(i128::MAX)),
            ],
        }],
    );

    assert_eq!(
        emit_category(&schema, "Term", &fixture),
        Err(EmitError::ShapeMismatch {
            expected: "a non-negative multiplicity that fits `usize`".to_string(),
            found: format!("the integer {}", i128::MAX),
        })
    );
}

#[test]
fn constructor_emitter_validates_native_byte_vectors_exactly() {
    let schema = recursive_schema();
    let valid = call(
        "BytesLit",
        vec![DebugNode::List(vec![
            DebugNode::Int(0),
            DebugNode::Int(127),
            DebugNode::Int(255),
        ])],
    );
    assert_eq!(
        emit_category(&schema, "Bytes", &valid),
        Ok("Bytes::BytesLit(vec![0u8, 127u8, 255u8])".to_string()),
    );

    for invalid in [DebugNode::Int(-1), DebugNode::Int(256)] {
        let fixture = call("BytesLit", vec![DebugNode::List(vec![invalid])]);
        assert!(matches!(
            emit_category(&schema, "Bytes", &fixture),
            Err(EmitError::ShapeMismatch { ref expected, .. })
                if expected == "a byte-array element in `0..=255`"
        ));
    }
}

#[test]
fn constructor_emitter_does_not_conflate_pathmap_set_and_map_modes() {
    let schema = recursive_schema();
    let fixture = call(
        "Path",
        vec![call(
            "Set",
            vec![call(
                "HashMapLit",
                vec![DebugNode::Map(vec![(
                    DebugNode::Ident("Leaf".to_string()),
                    DebugNode::Ident("Leaf".to_string()),
                )])],
            )],
        )],
    );
    assert!(matches!(
        emit_category(&schema, "Term", &fixture),
        Err(EmitError::ShapeMismatch { ref expected, .. })
            if expected == "the unit marker `()` for set-mode path membership"
    ));
}

#[test]
fn constructor_emitter_handles_twenty_thousand_nested_categories_on_a_small_stack() {
    std::thread::Builder::new()
        .name("constructor-emitter-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let schema = recursive_schema();
            let mut node = DebugNode::Ident("Leaf".to_string());
            for _ in 0..DEPTH {
                node = call("Wrap", vec![node]);
            }
            let rendered = emit_category(&schema, "Term", &node)
                .expect("the iterative emitter must accept its recursive fixture");
            assert!(rendered.starts_with("Term::Wrap(std::sync::Arc::new("));
            assert!(rendered.contains("Term::Leaf"));
            assert_eq!(rendered.matches("Term::Wrap(").count(), DEPTH);
        })
        .expect("the small-stack constructor-emitter thread must spawn")
        .join()
        .expect("the iterative constructor emitter must not overflow a 256 KiB stack");
}
