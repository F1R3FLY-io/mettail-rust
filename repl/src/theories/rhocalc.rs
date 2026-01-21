use crate::examples::TheoryName;
use crate::theory::{AscentResults, Rewrite, Term, TermInfo, Theory};
use anyhow::Result;
use std::any::Any;
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
    
    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>> {
        // Don't clear var cache - allows shared variables across env definitions
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
    
    // === Environment Support ===
    
    fn create_env(&self) -> Box<dyn Any + Send + Sync> {
        Box::new(RhoCalcEnv::new())
    }
    
    fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<()> {
        let rho_env = env
            .downcast_mut::<RhoCalcEnv>()
            .ok_or_else(|| anyhow::anyhow!("Invalid environment type"))?;
        
        let rho_term = term
            .as_any()
            .downcast_ref::<RhoTerm>()
            .ok_or_else(|| anyhow::anyhow!("Expected RhoTerm"))?;
        
        // Add to Proc environment
        rho_env.proc.set(name.to_string(), rho_term.0.clone());
        Ok(())
    }
    
    fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool> {
        let rho_env = env
            .downcast_mut::<RhoCalcEnv>()
            .ok_or_else(|| anyhow::anyhow!("Invalid environment type"))?;
        
        // Try to remove from both environments
        let proc_removed = rho_env.proc.remove(name).is_some();
        let name_removed = rho_env.name.remove(name).is_some();
        
        Ok(proc_removed || name_removed)
    }
    
    fn clear_env(&self, env: &mut dyn Any) {
        if let Some(rho_env) = env.downcast_mut::<RhoCalcEnv>() {
            rho_env.clear();
        }
    }
    
    fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>> {
        let rho_env = env
            .downcast_ref::<RhoCalcEnv>()
            .ok_or_else(|| anyhow::anyhow!("Invalid environment type"))?;
        
        let rho_term = term
            .as_any()
            .downcast_ref::<RhoTerm>()
            .ok_or_else(|| anyhow::anyhow!("Expected RhoTerm"))?;
        
        // Apply environment substitution
        let substituted = rho_term.0.substitute_env(rho_env);
        Ok(Box::new(RhoTerm(substituted)))
    }
    
    fn list_env(&self, env: &dyn Any) -> Vec<(String, String)> {
        let rho_env = match env.downcast_ref::<RhoCalcEnv>() {
            Some(e) => e,
            None => return Vec::new(),
        };
        
        let mut result = Vec::new();
        
        // List Proc bindings
        for (name, proc) in rho_env.proc.iter() {
            result.push((name.clone(), format!("{}", proc)));
        }
        
        // List Name bindings
        for (name, name_val) in rho_env.name.iter() {
            result.push((name.clone(), format!("{}", name_val)));
        }
        
        result
    }
    
    fn is_env_empty(&self, env: &dyn Any) -> bool {
        env.downcast_ref::<RhoCalcEnv>()
            .map(|e| e.is_empty())
            .unwrap_or(true)
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
