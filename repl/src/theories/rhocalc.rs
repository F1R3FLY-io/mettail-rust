use crate::examples::TheoryName;
use crate::theory::{AscentResults, Rewrite, Term, TermInfo, Theory};
use anyhow::Result;
use std::fmt;

// Import the theory definition from the theories crate
use mettail_theories::rhocalc::*;

/// RhoCalc theory implementation for REPL
pub struct RhoCalculusTheory;

impl Theory for RhoCalculusTheory {
    fn name(&self) -> TheoryName {
        TheoryName::RhoCalculus
    }

    fn categories(&self) -> Vec<String> {
        vec!["Proc".to_string(), "Name".to_string()]
    }

    fn constructor_count(&self) -> usize {
        8 // PZero, PInput, POutput, PPar, PDrop, NQuote, NVar, PVar
    }

    fn equation_count(&self) -> usize {
        1 // (NQuote (PDrop N)) == N
    }

    fn rewrite_count(&self) -> usize {
        3 // Communication, Drop, Congruence
    }

    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>> {
        mettail_runtime::clear_var_cache();
        let parser = rhocalc::ProcParser::new();
        let proc = parser
            .parse(input)
            .map_err(|e| anyhow::anyhow!("Parse error: {:?}", e))?;
        Ok(Box::new(RhoTerm(proc)))
    }

    fn run_ascent(&self, term: Box<dyn Term>) -> Result<AscentResults> {
        use ascent::*;

        // Downcast to RhoTerm
        let rho_term = term
            .as_any()
            .downcast_ref::<RhoTerm>()
            .ok_or_else(|| anyhow::anyhow!("Expected RhoTerm"))?;

        let initial_proc = rho_term.0.clone();

        // Run Ascent with the generated source
        let prog = ascent_run! {
            include_source!(rhocalc_source);

            proc(initial_proc.clone());
        };

        // Extract results
        let all_procs: Vec<Proc> = prog.proc.iter().map(|(p,):&(Proc,)| p.clone()).collect();
        let rewrites: Vec<(Proc, Proc)> = prog
            .rw_proc
            .iter()
            .map(|(from, to)| (from.clone(), to.clone()))
            .collect();

        // Build term info
        let mut term_infos = Vec::new();

        for proc in &all_procs {
            let term_id = compute_term_id(proc);
            let has_rewrites = rewrites.iter().any(|(from, _)| from == proc);

            term_infos.push(TermInfo {
                term_id,
                display: format!("{}", proc),
                is_normal_form: !has_rewrites,
            });
        }

        // Build rewrite list
        let rewrite_list: Vec<Rewrite> = rewrites
            .iter()
            .map(|(from, to)| Rewrite {
                from_id: compute_term_id(from),
                to_id: compute_term_id(to),
                rule_name: Some("rewrite".to_string()),
            })
            .collect();

        let equivalences = Vec::new(); // TODO: Extract from prog.eq_proc

        Ok(AscentResults {
            all_terms: term_infos,
            rewrites: rewrite_list,
            equivalences,
        })
    }

    fn format_term(&self, term: &dyn Term) -> String {
        format!("{}", term)
    }
}

/// Wrapper for Proc that implements Term
#[derive(Clone)]
struct RhoTerm(Proc);

impl Term for RhoTerm {
    fn clone_box(&self) -> Box<dyn Term> {
        Box::new(self.clone())
    }

    fn term_id(&self) -> u64 {
        compute_term_id(&self.0)
    }

    fn term_eq(&self, other: &dyn Term) -> bool {
        if let Some(other_rho) = other.as_any().downcast_ref::<RhoTerm>() {
            self.0 == other_rho.0
        } else {
            false
        }
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

impl fmt::Display for RhoTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for RhoTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// Compute a unique ID for a term (simple hash for now)
fn compute_term_id(proc: &Proc) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut hasher = DefaultHasher::new();
    proc.hash(&mut hasher);
    hasher.finish()
}
