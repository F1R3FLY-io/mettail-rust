use crate::examples::TheoryName;
use crate::theory::{AscentResults, Rewrite, Term, TermInfo, Theory};
use anyhow::Result;
use std::cell::RefCell;
use std::fmt;

// Import the theory definition from the theories crate
use mettail_theories::rhocalc::*;

thread_local! {
    static PROC_ENV: RefCell<RhoCalcProcEnv> = RefCell::new(RhoCalcProcEnv::new());
    static NAME_ENV: RefCell<RhoCalcNameEnv> = RefCell::new(RhoCalcNameEnv::new());
}

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

        // Handle assignments: evaluate RHS and update environment, but return the term
        // so rewrites can still be shown
        if let Proc::Assign(var, rhs) = &proc {
            // Get current environment
            let proc_env_facts: Vec<(String, Proc)> = PROC_ENV.with(|env| {
                env.borrow().env_to_facts()
            });
            let name_env_facts: Vec<(String, Name)> = NAME_ENV.with(|env| {
                env.borrow().env_to_facts()
            });

            // Evaluate RHS using Ascent
            use ascent::*;
            let prog = ascent_run! {
                include_source!(rhocalc_source);

                proc(rhs.as_ref().clone());

                // Seed environment facts
                env_var_proc(n.clone(), v) <-- for (n, v) in proc_env_facts.clone();
                env_var_name(n.clone(), v) <-- for (n, v) in name_env_facts.clone();
            };

            // Find normal form of RHS by following rewrite chains
            let rewrites: Vec<(Proc, Proc)> = prog
                .rw_proc
                .iter()
                .map(|(from, to)| (from.clone(), to.clone()))
                .collect();

            // Start from the RHS and follow rewrite chains to find normal form
            let mut current = rhs.as_ref().clone();
            loop {
                // Find a rewrite from current term
                if let Some((_, next)) = rewrites.iter().find(|(from, _)| from == &current) {
                    current = next.clone();
                } else {
                    // No more rewrites - this is the normal form
                    break;
                }
            }

            // Update environment
            if let Some(var_name) = match var {
                mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)) => {
                    fv.pretty_name.clone()
                }
                _ => None,
            } {
                PROC_ENV.with(|env| {
                    env.borrow_mut().set(var_name, current.clone());
                });
            }
        }

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

        // Get environment facts from thread-local storage
        let proc_env_facts: Vec<(String, Proc)> = PROC_ENV.with(|env| {
            env.borrow().env_to_facts()
        });
        let name_env_facts: Vec<(String, Name)> = NAME_ENV.with(|env| {
            env.borrow().env_to_facts()
        });

        // Run Ascent with the generated source
        let prog = ascent_run! {
            include_source!(rhocalc_source);

            proc(initial_proc.clone());

            // Seed environment facts (use category-specific relation names)
            env_var_proc(n.clone(), v) <-- for (n, v) in proc_env_facts.clone();
            env_var_name(n.clone(), v) <-- for (n, v) in name_env_facts.clone();
        };

        // Extract results
        let all_procs: Vec<Proc> = prog.proc.iter().map(|(p,)| p.clone()).collect();
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
