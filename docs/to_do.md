update main docs
- architecture/main_goals are 2 months old
- replace [docs/design/made] with [docs/manual]

complete logic
- conjunction of premises
- eq congruence for terms with collection and binding
- generic common relations (path,normal_form,etc.)

fix bugs
- repl display types of free/bound vars

improve term generation
- guide by redex formation
- generate contexts for the LTS

improve repl
- make any result the new current_term
- display auto-generated logic (Var,Lam/App,etc)

build out more languages + programs
- rholang
- mettail
- rust
- ...?

code improvement
- split up "ast_code" [macros/src/lib.rs]
- phase out BNF
- replace "category" with "lang_type"
- organize [languages/src/generated]

performance
- optimize datalog rules
- laziness
- ascent_par!

rspace integration

language composition

language translation