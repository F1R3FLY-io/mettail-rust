use mettail_macros::theory;
use mettail_runtime;
use ascent_byods_rels::*;
use std::time::Instant;
// Note: Pretty printing moved to REPL. Use plain Display for now.
// use mettail_repl::pretty::format_term_pretty;
use ascent::*;

theory! {
    name: SpaceCalc,
    exports {
        Proc
        Name
    },
    terms {
        PZero . Proc ::= "0" ;
        PDrop . Proc ::= "*" Name ;
        POutput . Proc ::= Name "!" "(" Proc ")" ;
        PInput . Proc ::= "for" "(" Name "->" <Name> ")" "{" Proc "}" ;

        PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;

        PUNm . Proc ::= "U" "(" Name ")" ;
        PComm . Proc ::= "COMM" "(" <Proc> "." Proc ")" ;
        NQuote . Name ::= "@" "(" Proc "," <Proc> "." Proc ")" ;

        NVar . Name ::= Var ;
        PVar . Proc ::= Var ;
    },
    equations {
        // @(*(-))?
    },
    rewrites {
        (PPar {(PUNm N), (PDrop (NQuote Q x K))})
            => (PPar {(PComm x K), (POutput N Q)});

        // (PPar {(PComm y K), (PInput N x P), (POutput N Q)})
        //     => (PPar {(subst P (PDrop x) (subst K y Q))});

        if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest});
    }
}

fn main() {
    let start_time = Instant::now();
    let vars = vec!["a".to_string(), "b".to_string(), "c".to_string()];
    println!("=== Space Calculus ===");
    let redex = Proc::generate_random_at_depth(&vars, 12, 6);
    println!("Term: {}", redex); // Using plain Display instead of pretty formatting
}