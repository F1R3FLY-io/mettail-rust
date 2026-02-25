> cargo run

╔════════════════════════════════════════════════════════════╗
║                   MeTTaIL Term Explorer                    ║
║                      Version 0.1.0                         ║
╚════════════════════════════════════════════════════════════╝

Type 'help' for available commands.

mettail> help

Available commands:

  Language Management:
    languages        Show available languages
    lang <name>  Open language
    {lang_name}> info              Show language information

  Term Input:
    exec <term>    Execute a program (direct evaluation → result)
    step <term>    Step-by-step: show initial term, use apply 0 to reduce
    example <name>    Load example program
    list-examples    List available examples

  Environment:
    <name> = <term> Define a named term
    save <name>      Save current term to environment
    env               Show all environment bindings
    clear <name>    Remove a binding
    clear-all         Clear all bindings
    load-env <file> Load declarations from file

  Type Inspection:
    type              Show type of current term
    types             Show all variable types
    typeof <var>  Show type of specific variable

  Navigation:
    rewrites           List rewrites from current term
    rewrites-all         List all rewrites
    normal-forms        Show normal forms
    apply <N> Apply one rewrite from current term (use after step)
    goto <N>              Go to normal form N

  Relations:
    relations         List all computed relations
    relation <name> Show tuples in a relation

  Query:
    head(args) <-- body.  Run a Datalog rule over step results (e.g. query(result) <-- path(current_term, result), !rw_proc(result, _)).

  General:
    help              Show this help
    quit, exit        Exit REPL