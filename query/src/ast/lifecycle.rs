//! Stack-safe lifecycle operations for recursive query body atoms.

use super::BodyAtom;
use std::fmt;

impl Clone for BodyAtom {
    fn clone(&self) -> Self {
        let mut depth = 0;
        let mut cursor = self;
        while let BodyAtom::Negation(inner) = cursor {
            depth += 1;
            cursor = inner;
        }
        let mut cloned = match cursor {
            BodyAtom::Relation { name, terms } => {
                BodyAtom::Relation { name: name.clone(), terms: terms.clone() }
            },
            BodyAtom::If(expression) => BodyAtom::If(expression.clone()),
            BodyAtom::Negation(_) => unreachable!("query clone spine stopped on a wrapper"),
        };
        for _ in 0..depth {
            cloned = BodyAtom::Negation(Box::new(cloned));
        }
        cloned
    }
}

impl Drop for BodyAtom {
    fn drop(&mut self) {
        let mut next = match self {
            BodyAtom::Negation(inner) => Some(*std::mem::replace(
                inner,
                Box::new(BodyAtom::Relation { name: String::new(), terms: Vec::new() }),
            )),
            BodyAtom::Relation { .. } | BodyAtom::If(_) => None,
        };
        while let Some(mut atom) = next {
            next = match &mut atom {
                BodyAtom::Negation(inner) => Some(*std::mem::replace(
                    inner,
                    Box::new(BodyAtom::Relation { name: String::new(), terms: Vec::new() }),
                )),
                BodyAtom::Relation { .. } | BodyAtom::If(_) => None,
            };
        }
    }
}

impl fmt::Debug for BodyAtom {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut depth = 0;
        let mut cursor = self;
        while let BodyAtom::Negation(inner) = cursor {
            formatter.write_str("Negation(")?;
            depth += 1;
            cursor = inner;
        }
        match cursor {
            BodyAtom::Relation { name, terms } => {
                write!(formatter, "Relation {{ name: {name:?}, terms: {terms:?} }}")?;
            },
            BodyAtom::If(expression) => write!(formatter, "If({expression:?})")?,
            BodyAtom::Negation(_) => unreachable!("query debug spine stopped on a wrapper"),
        }
        for _ in 0..depth {
            formatter.write_str(")")?;
        }
        Ok(())
    }
}
