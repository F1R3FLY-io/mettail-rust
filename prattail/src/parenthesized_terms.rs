use std::collections::HashMap;
use std::ops::Range;

#[derive(Debug)]
struct Application {
    close: usize,
    arguments: Range<usize>,
}

#[derive(Debug)]
struct OpenApplication {
    open: usize,
    commas: Vec<usize>,
}

pub(crate) enum TermView<'a> {
    Empty,
    Atom(&'a str),
    Application {
        head: &'a str,
        arguments: &'a [Range<usize>],
    },
}

/// A single-pass delimiter index for the compact `head(arg, ...)` term syntax.
///
/// The source is never copied. Each parenthesis and comma is indexed once, and
/// consumers can then walk nested terms with explicit continuation frames
/// without rescanning complete descendant substrings at every ancestor.
pub(crate) struct ParenthesizedTerms<'a> {
    source: &'a str,
    applications: HashMap<usize, Application>,
    arguments: Vec<Range<usize>>,
}

impl<'a> ParenthesizedTerms<'a> {
    pub(crate) fn new(source: &'a str) -> Result<Self, ()> {
        let mut open = Vec::<OpenApplication>::new();
        let mut applications = HashMap::new();
        let mut arguments = Vec::new();

        for (offset, character) in source.char_indices() {
            match character {
                '(' => open.push(OpenApplication { open: offset, commas: Vec::new() }),
                ',' => {
                    if let Some(application) = open.last_mut() {
                        application.commas.push(offset);
                    }
                },
                ')' => {
                    let application = open.pop().ok_or(())?;
                    let argument_start = arguments.len();
                    let inner = &source[application.open + 1..offset];
                    if !inner.trim().is_empty() {
                        let mut start = application.open + 1;
                        for comma in application.commas {
                            arguments.push(start..comma);
                            start = comma + 1;
                        }
                        arguments.push(start..offset);
                    }
                    applications.insert(
                        application.open,
                        Application {
                            close: offset,
                            arguments: argument_start..arguments.len(),
                        },
                    );
                },
                _ => {},
            }
        }

        if !open.is_empty() {
            return Err(());
        }
        Ok(Self { source, applications, arguments })
    }

    pub(crate) fn root(&self) -> Range<usize> {
        0..self.source.len()
    }

    pub(crate) fn is_empty(&self, range: &Range<usize>) -> bool {
        self.source[range.clone()].trim().is_empty()
    }

    pub(crate) fn view(&self, range: Range<usize>) -> Result<TermView<'_>, ()> {
        let range = self.trimmed_range(range);
        if range.is_empty() {
            return Ok(TermView::Empty);
        }
        let token = &self.source[range.clone()];
        let Some(relative_open) = token.find('(') else {
            return Ok(TermView::Atom(token));
        };
        let open = range.start + relative_open;
        let application = self.applications.get(&open).ok_or(())?;
        if application.close + 1 != range.end {
            return Err(());
        }
        Ok(TermView::Application {
            head: &self.source[range.start..open],
            arguments: &self.arguments[application.arguments.clone()],
        })
    }

    fn trimmed_range(&self, range: Range<usize>) -> Range<usize> {
        let raw = &self.source[range.clone()];
        let trimmed_start = raw.trim_start();
        let start = range.start + raw.len() - trimmed_start.len();
        let trimmed = trimmed_start.trim_end();
        start..start + trimmed.len()
    }
}
