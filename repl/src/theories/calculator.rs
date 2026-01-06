use crate::examples::TheoryName;
use crate::theory::{AscentResults, Rewrite, Term, TermInfo, Theory};
use anyhow::Result;
use std::cell::RefCell;
use std::fmt;

// Import the theory definition from the theories crate
use mettail_theories::calculator::*;

thread_local! {
    static CALC_ENV: RefCell<CalculatorIntEnv> = RefCell::new(CalculatorIntEnv::new());
}

/// Calculator theory implementation for REPL
pub struct CalculatorTheory;

impl Theory for CalculatorTheory {
    fn name(&self) -> TheoryName {
        TheoryName::Calculator
    }

    fn categories(&self) -> Vec<String> {
        vec!["Int".to_string(), "Ident".to_string()]
    }

    fn constructor_count(&self) -> usize {
        5 // NumLit, Add, Sub, IVar, Assign
    }

    fn equation_count(&self) -> usize {
        0 // No equations defined
    }

    fn rewrite_count(&self) -> usize {
        1 // Variable substitution rewrite rule
    }

    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>> {
        mettail_runtime::clear_var_cache();

        let trimmed = input.trim();

        // Parse to Int AST
        let parser = calculator::IntParser::new();
        let expr = parser
            .parse(trimmed)
            .map_err(|e| anyhow::anyhow!("Parse error: {:?}", e))?;

        // Handle assignments: evaluate RHS and update environment, but return the term
        // so rewrites can still be shown
        if let Int::Assign(var, rhs) = &expr {
            // Get current environment
            let env_facts: Vec<(String, i32)> = CALC_ENV.with(|env| {
                env.borrow().env_to_facts()
                    .into_iter()
                    .map(|(name, val)| {
                        let i32_val = match val {
                            Int::NumLit(v) => v,
                            _ => return Err(anyhow::anyhow!("Environment value must be a NumLit")),
                        };
                        Ok((name, i32_val))
                    })
                    .collect::<Result<Vec<_>>>()
            })
            .map_err(|e| anyhow::anyhow!("Failed to convert environment: {}", e))?;

            // Evaluate RHS using Ascent
            use ascent::*;
            let prog = ascent_run! {
                include_source!(calculator_source);

                int(rhs.as_ref().clone());

                env_var_int(n.clone(), v) <-- for (n, v) in env_facts.clone();
            };

            // Find normal form of RHS
            let rewrites: Vec<(Int, Int)> = prog
                .rw_int
                .iter()
                .map(|(from, to)| (from.clone(), to.clone()))
                .collect();

            let mut current = rhs.as_ref().clone();
            while let Some((_, next)) = rewrites.iter().find(|(from, _)| from == &current) {
                current = next.clone();
            }

            // Extract value from normal form
            let val = match &current {
                Int::NumLit(v) => *v,
                _ => {
                    // Try to evaluate if not a NumLit
                    // Check if the term contains any variables
                    if matches!(current, Int::IVar(_)) {
                        return Err(anyhow::anyhow!("Assignment RHS contains undefined variables"));
                    }
                    current.eval()
                }
            };

            // Update environment
            if let Some(var_name) = match var {
                mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)) => {
                    fv.pretty_name.clone()
                }
                _ => None,
            } {
                CALC_ENV.with(|env| {
                    env.borrow_mut().set(var_name, Int::NumLit(val));
                });
            }
        }

        // Return the parsed term (not evaluated) so rewrites can be shown
        Ok(Box::new(CalcTerm(expr)) as Box<dyn Term>)
    }

    fn run_ascent(&self, term: Box<dyn Term>) -> Result<AscentResults> {
        use ascent::*;

        let calc_term = term
            .as_any()
            .downcast_ref::<CalcTerm>()
            .ok_or_else(|| anyhow::anyhow!("Expected CalcTerm"))?;

        let initial_int = calc_term.0.clone();

        // Get environment facts from thread-local storage - convert Int enum to i32 for Ascent
        let env_facts: Vec<(String, i32)> = CALC_ENV.with(|env| {
            env.borrow().env_to_facts()
                .into_iter()
                .map(|(name, val)| {
                    // Extract i32 from Int enum (NumLit variant)
                    let i32_val = match val {
                        Int::NumLit(v) => v,
                        _ => return Err(anyhow::anyhow!("Environment value must be a NumLit"))?,
                    };
                    Ok((name, i32_val))
                })
                .collect::<Result<Vec<_>>>()
        })
        .map_err(|e| anyhow::anyhow!("Failed to convert environment: {}", e))?;

        // Run Ascent with the generated source
        // Seed env_var facts using a rule that iterates over the collection
        let prog = ascent_run! {
            include_source!(calculator_source);

            int(initial_int.clone());

            // Seed environment facts from the vector
            env_var_int(n.clone(), v) <-- for (n, v) in env_facts.clone();
        };

        // Extract results from Ascent relations
        let all_ints: Vec<Int> = prog.int.iter().map(|(i,)| i.clone()).collect();
        let rewrites: Vec<(Int, Int)> = prog
            .rw_int
            .iter()
            .map(|(from, to)| (from.clone(), to.clone()))
            .collect();

        // Build term info (similar to rhocalc/ambient)
        let mut term_infos = Vec::new();
        for int_term in &all_ints {
            let term_id = compute_term_id(int_term);
            let has_rewrites = rewrites.iter().any(|(from, _)| from == int_term);

            term_infos.push(TermInfo {
                term_id,
                display: format!("{}", int_term),
                is_normal_form: !has_rewrites,
            });
        }

        // Build rewrite list with proper labeling
        let rewrite_list: Vec<Rewrite> = rewrites
            .iter()
            .map(|(from, to)| {
                // Determine the rule name based on the rewrite pattern
                let rule_name = match (from, to) {
                    // Semantic rewrites: Add/Sub with NumLit operands -> NumLit result
                    (Int::Add(left, right), Int::NumLit(_)) => {
                        if matches!(left.as_ref(), Int::NumLit(_))
                            && matches!(right.as_ref(), Int::NumLit(_))
                        {
                            Some("add".to_string())
                        } else {
                            Some("var_substitution".to_string())
                        }
                    }
                    (Int::Sub(left, right), Int::NumLit(_)) => {
                        if matches!(left.as_ref(), Int::NumLit(_))
                            && matches!(right.as_ref(), Int::NumLit(_))
                        {
                            Some("subtract".to_string())
                        } else {
                            Some("var_substitution".to_string())
                        }
                    }
                    // Variable substitution: IVar -> NumLit
                    (Int::IVar(_), Int::NumLit(_)) => Some("var_substitution".to_string()),
                    // Congruence rewrites (propagating through Add/Sub/Assign)
                    (Int::Add(_, _), Int::Add(_, _)) => Some("congruence".to_string()),
                    (Int::Sub(_, _), Int::Sub(_, _)) => Some("congruence".to_string()),
                    (Int::Assign(_, _), Int::Assign(_, _)) => Some("congruence".to_string()),
                    // Default fallback
                    _ => Some("rewrite".to_string()),
                };

                Rewrite {
                    from_id: compute_term_id(&from),
                    to_id: compute_term_id(&to),
                    rule_name,
                }
            })
            .collect();

        Ok(AscentResults {
            all_terms: term_infos,
            rewrites: rewrite_list,
            equivalences: Vec::new(), // Calculator has no equations
        })
    }

    fn format_term(&self, term: &dyn Term) -> String {
        if let Some(calc_term) = term.as_any().downcast_ref::<CalcTerm>() {
            // Try to evaluate the term
            match std::panic::catch_unwind(|| calc_term.0.eval()) {
                Ok(value) => format!("{}", value),
                Err(_) => format!("{}", calc_term.0),
            }
        } else {
            format!("{}", term)
        }
    }
}

/// Wrapper for Int AST that implements Term
#[derive(Clone)]
struct CalcTerm(Int);

impl Term for CalcTerm {
    fn clone_box(&self) -> Box<dyn Term> {
        Box::new(self.clone())
    }

    fn term_id(&self) -> u64 {
        compute_term_id(&self.0)
    }

    fn term_eq(&self, other: &dyn Term) -> bool {
        if let Some(other_calc) = other.as_any().downcast_ref::<CalcTerm>() {
            self.0 == other_calc.0
        } else {
            false
        }
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

impl fmt::Display for CalcTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for CalcTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// Compute a unique ID for an Int term
fn compute_term_id(term: &Int) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut hasher = DefaultHasher::new();
    term.hash(&mut hasher);
    hasher.finish()
}
