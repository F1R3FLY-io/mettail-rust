use mettail_macros::language;

language! {
    name: PrefixOpenerUnion,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
        parse_only: true,
        hosted_in: "tests/definitions/prefix_opener_union.rs",
    },

    types {
        noadmit Expr
    },

    terms {
        Atom . |- "x" : Expr;
        Pipe . |- "|" : Expr;

        SquareComma . xs:HashBag(Expr) |- "[" xs.*sep(",") "]" : Expr;
        SquareSemicolon . xs:HashBag(Expr) |- "[" xs.*sep(";") "]" : Expr;
        SquareNullary . |- "[" "]" : Expr;

        Round . xs:HashBag(Expr) |- "(" xs.*sep(",") ")" : Expr;
        RoundNullary . |- "(" ")" : Expr;

        Curly . xs:HashBag(Expr) |- "{" xs.*sep(",") "}" : Expr;
        CurlyNullary . |- "{" "}" : Expr;

        Compound . xs:HashBag(Expr) |- "{|" xs.*sep(",") "|}" : Expr;
        CompoundNullary . |- "{|" "|}" : Expr;

        HashOpen . xs:HashBag(Expr) |- "#{" xs.*sep(",") "}" : Expr;
        HashNullary . |- "#{" "}" : Expr;

        MapRound . xs:HashBag(Expr) |- "Map" "(" xs.*sep(",") ")" : Expr;
        MapRoundNullary . |- "Map" "(" ")" : Expr;

        Mixed . xs:HashBag(Expr) |- "(" xs.*sep(",") "]" : Expr;
        MixedNullary . |- "(" "]" : Expr;

        Deep . xs:HashBag(Expr) |- "<" xs.*sep(",") ">" : Expr;
        Pair . left:Expr, right:Expr |- "pair" "(" left "," right ")" : Expr;
        Sequence . xs:Vec(Expr) |- "seq" "(" xs.*sep(",") ")" : Expr;
    },
}
