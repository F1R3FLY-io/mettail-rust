use super::*;
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use mettail_runtime::{FltHole as SourceHole, FltHoleId, FltSourceRange, FltTemplatePiece};
use prost::Message;

fn source(open: &str, close: &str) -> FltNode {
    FltNode::from_structural_parts(
        "guest".into(),
        "Expr".into(),
        open.into(),
        "a${x:Text}b${x:Text}".into(),
        vec![SourceHole {
            id: FltHoleId(0),
            name: "x".into(),
            category: Some("Text".into()),
            first_occurrence: FltSourceRange::new(1, 10),
        }],
        vec![
            FltTemplatePiece::Text {
                text: "a".into(),
                range: FltSourceRange::new(0, 1),
            },
            FltTemplatePiece::Hole {
                id: FltHoleId(0),
                range: FltSourceRange::new(1, 10),
            },
            FltTemplatePiece::Text {
                text: "b".into(),
                range: FltSourceRange::new(10, 11),
            },
            FltTemplatePiece::Hole {
                id: FltHoleId(0),
                range: FltSourceRange::new(11, 20),
            },
        ],
        close.into(),
        7,
    )
    .expect("structural fixture")
}

fn request(
    source: &FltNode,
    policy: SourcePreparation,
    reserve: &mut StorageReservation<'_>,
) -> Result<Par, RholangAstLowerError> {
    let template = source.stage(FltPolarity::NegativePattern);
    let (pieces, holes) = template_parts(template, policy, reserve)?;
    // These are deliberately caller-owned arguments, constructed before this
    // request adapter. Their index-sized construction is not charged here.
    let handle = new_boundvar_par(3, Vec::new(), false);
    let reply = new_boundvar_par(0, Vec::new(), false);
    pattern_request(handle, &pieces, &holes, template.category, reply, policy, reserve)
}

#[test]
fn template_projection_and_pattern_request_preserve_exact_bytes_and_occurrences() {
    for (open, close) in [("`", "`"), ("```", "```"), ("{", "}")] {
        let source = source(open, close);
        let unchanged = source.clone();
        let expected = request(&source, SourcePreparation::Original, &mut |_, _| {
            panic!("original projection and encoder must not reserve")
        })
        .unwrap();
        let actual = request(&source, SourcePreparation::Checked, &mut |_, _| Ok(())).unwrap();
        assert_eq!(actual.encode_to_vec(), expected.encode_to_vec());
        let (pieces, holes) = template_parts(
            source.stage(FltPolarity::PositiveConstruction),
            SourcePreparation::Checked,
            &mut |_, _| Ok(()),
        )
        .unwrap();
        assert_eq!(
            pieces,
            vec![
                RuntimeTemplatePiece::Text("a".into()),
                RuntimeTemplatePiece::Hole(0),
                RuntimeTemplatePiece::Text("b".into()),
                RuntimeTemplatePiece::Hole(0),
            ]
        );
        assert_eq!(
            holes,
            vec![NamedRuntimeTemplateHole {
                id: 0,
                name: "x".into(),
                category: Some("Text".into()),
            }]
        );
        assert_eq!(source, unchanged);
    }
}

#[test]
fn template_and_pattern_request_all_cuts_preserve_the_paid_prefix_and_source() {
    let source = source("`", "`");
    let unchanged = source.clone();
    let mut trace = Vec::new();
    let expected = request(&source, SourcePreparation::Checked, &mut |w, u| {
        trace.push((w, u));
        Ok(())
    })
    .unwrap();
    for cut in 0..trace.len() {
        let mut prefix = Vec::new();
        let result = request(&source, SourcePreparation::Checked, &mut |w, u| {
            if prefix.len() == cut {
                return Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled));
            }
            prefix.push((w, u));
            Ok(())
        });
        assert_eq!(
            result,
            Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
        );
        assert_eq!(prefix, trace[..cut]);
        assert_eq!(source, unchanged);
        assert_eq!(
            request(&source, SourcePreparation::Checked, &mut |_, _| Ok(()))
                .unwrap()
                .encode_to_vec(),
            expected.encode_to_vec()
        );
    }
    let work = trace.iter().map(|(w, _)| *w as u64).sum::<u64>();
    let units = trace.iter().map(|(_, u)| *u).sum::<usize>();
    for (work_limit, unit_limit, accepted) in [
        (work, units, true),
        (work - 1, units, false),
        (work, units - 1, false),
        (0, 0, false),
    ] {
        let mut used = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut used, work_limit, unit_limit, &mut cancel);
        let result = request(&source, SourcePreparation::Checked, &mut |w, u| {
            budget
                .charge(w, u)
                .map_err(RholangAstLowerError::Preparation)
        });
        assert_eq!(result.is_ok(), accepted);
    }
}

#[test]
fn pattern_wire_metadata_arithmetic_refuses_before_the_encoder() {
    assert_eq!(
        list(usize::MAX, 1, SourcePreparation::Checked, &mut |_, _| panic!(
            "overflow before debit"
        )),
        Err(RholangAstLowerError::PreparationSizeOverflow),
    );
    assert_eq!(
        list(1, usize::MAX, SourcePreparation::Checked, &mut |_, _| panic!(
            "overflow before debit"
        )),
        Err(RholangAstLowerError::PreparationSizeOverflow),
    );
}
