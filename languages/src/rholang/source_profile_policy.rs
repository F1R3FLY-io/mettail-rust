//! The single closed Rholang source-profile table.
//!
//! Each row names an actual generated constructor and all its original field
//! slots. Rust types are consumed by the macro census; transitions are consumed
//! by both the census and the typed host policy. Opaque slots contain no host
//! category child. This table is deliberately independent of parser machinery.
//!
//! T/N/P/PN/G/D select term/name/pattern/name-pattern/guard/declaration roles.
//! I inherits the incoming role. Q maps a name-pattern quotation to a pattern
//! and other quotations to terms. B preserves guard context, otherwise term.

macro_rules! rholang_source_profile_rows {
    ($consumer:ident) => {
        $consumer! {
            Proc::PZero => [];
            Proc::POutputNilEmpty => [];
            Proc::PPersistOutputNilEmpty => [];
            Proc::MapEmpty => [];
            Proc::PVar => [OrdVar => Opaque];
            Proc::PDrop => [Arc<Name> => N];
            Proc::PPar => [HashBag<Proc> => I];
            Proc::PParInfix => [Arc<Proc> => I, Arc<Proc> => I];
            Proc::POutput => [Arc<Name> => N, Arc<Proc> => T];
            Proc::PPersistOutput => [Arc<Name> => N, Arc<Proc> => T];
            Proc::POutputQuoted => [Arc<Name> => N, Arc<Proc> => T];
            Proc::POutputShort => [Arc<Proc> => T, Arc<Proc> => T];
            Proc::PPersistOutputShort => [Arc<Proc> => T, Arc<Proc> => T];
            Proc::POutputEmpty => [Arc<Name> => N];
            Proc::PPersistOutputEmpty => [Arc<Name> => N];
            Proc::POutputQuotedEmpty => [Arc<Name> => N];
            Proc::POutput2Plus => [Arc<Name> => N, Arc<Proc> => T, Vec<Proc> => T];
            Proc::PPersistOutput2Plus => [Arc<Name> => N, Arc<Proc> => T, Vec<Proc> => T];
            Proc::POutputQuoted2Plus => [Arc<Name> => N, Arc<Proc> => T, Vec<Proc> => T];
            Proc::POutputShortEmpty => [Arc<Proc> => T];
            Proc::PPersistOutputShortEmpty => [Arc<Proc> => T];
            Proc::POutputNil => [Arc<Proc> => T];
            Proc::PPersistOutputNil => [Arc<Proc> => T];
            Proc::POutputShort2Plus => [Arc<Proc> => T, Arc<Proc> => T, Vec<Proc> => T];
            Proc::PPersistOutputShort2Plus => [Arc<Proc> => T, Arc<Proc> => T, Vec<Proc> => T];
            Proc::POutputNil2Plus => [Arc<Proc> => T, Vec<Proc> => T];
            Proc::PPersistOutputNil2Plus => [Arc<Proc> => T, Vec<Proc> => T];
            Proc::PNew => [Scope<Vec<Binder<String>>,Arc<Proc>> => T];
            Proc::PNewUris => [Vec<Uri> => I, Scope<Vec<Binder<String>>,Arc<Proc>> => T];
            Proc::PForUser => [Vec<ForRow> => I, Arc<Proc> => T];
            ForRow::ForRowSingleNoWhere => [Arc<InputBind> => I];
            ForRow::ForRowSingleWhere => [Arc<InputBind> => I, Arc<Proc> => G];
            ForRow::ForRowNoWhere => [Arc<InputBind> => I, Vec<InputBind> => I];
            ForRow::ForRowWhere => [Arc<InputBind> => I, Vec<InputBind> => I, Arc<Proc> => G];
            InputBind::InputBind => [Arc<Name> => PN, Arc<Name> => N];
            InputBind::InputBindPersistent => [Arc<Name> => PN, Arc<Name> => N];
            InputBind::InputBindPolyadic => [Arc<Name> => PN, Vec<Name> => PN, Arc<Name> => N];
            InputBind::InputBindPersistentPolyadic => [Arc<Name> => PN, Vec<Name> => PN, Arc<Name> => N];
            InputBind::InputBindEmpty => [Arc<Name> => N];
            InputBind::InputBindEmptyPersistent => [Arc<Name> => N];
            InputBind::InputBindQuoted => [Arc<Proc> => P, Arc<Name> => N];
            InputBind::InputBindQuotedPersistent => [Arc<Proc> => P, Arc<Name> => N];
            Name::NVar => [OrdVar => Opaque];
            Name::NQuoteNil => [];
            Name::NParen => [Arc<Name> => I];
            Name::NQuote => [Arc<Proc> => Q];
            Name::NQuoteShort => [Arc<Proc> => Q];
            Proc::CastInt => [Arc<Int> => I];
            Proc::CastBool => [Arc<Bool> => I];
            Proc::CastStr => [Arc<Str> => I];
            Proc::CastList => [Arc<List> => I];
            Proc::CastMap => [Arc<Map> => I];
            Int::NumLit => [i64 => Opaque];
            Int::NegInt => [Arc<Int> => I];
            Bool::BoolLit => [bool => Opaque];
            Str::StringLit => [String => Opaque];
            List::ListLit => [Vec<Proc> => I];
            Map::MapLit => [HashMapLit<Proc,Proc> => I];
            Proc::MethodCall => [Arc<Proc> => T, String => Opaque, Vec<Proc> => T];
            Proc::Eq => [Arc<Proc> => T, Arc<Proc> => T];
            Proc::Ne => [Arc<Proc> => T, Arc<Proc> => T];
            Proc::Lt => [Arc<Proc> => T, Arc<Proc> => T];
            Proc::Gt => [Arc<Proc> => T, Arc<Proc> => T];
            Proc::LtEq => [Arc<Proc> => T, Arc<Proc> => T];
            Proc::GtEq => [Arc<Proc> => T, Arc<Proc> => T];
            Proc::And => [Arc<Proc> => B, Arc<Proc> => B];
            Proc::Or => [Arc<Proc> => B, Arc<Proc> => B];
            Proc::Implies => [Arc<Proc> => B, Arc<Proc> => B];
            Proc::Not => [Arc<Proc> => B];
            Proc::PFlt => [Arc<FltNode> => Opaque];
            Proc::PFltFence => [Arc<FltNode> => Opaque];
            Proc::PFltBrace => [Arc<FltNode> => Opaque];
            Uri::UriText => [String => Opaque];
            Proc::DdlModule => [String => Opaque, Vec<DdlModuleItem> => D];
            Proc::DdlModuleImported => [Arc<DdlImports> => D, String => Opaque, Vec<DdlModuleItem> => D];
            Proc::DdlTheory => [String => Opaque, Vec<DdlParam> => D, Arc<DdlTheoryExpr> => D];
            DdlModuleItem::DdlModuleTheoryItem => [Arc<DdlTheoryExpr> => D];
            DdlModuleItem::DdlModuleProcItem => [Arc<Proc> => T];
            DdlParam::DdlParamDecl => [String => Opaque, Arc<DdlPath> => D];
            DdlPath::DdlPathQualified => [String => Opaque, Arc<DdlPath> => D];
            DdlPath::DdlPathName => [String => Opaque];
            DdlImports::DdlImportsNonEmpty => [Arc<DdlImport> => D, Vec<DdlImport> => D];
            DdlImport::DdlImportModuleAs => [String => Opaque, String => Opaque];
            DdlImport::DdlImportFromModule => [String => Opaque, String => Opaque];
            DdlTheoryExpr::DdlTheoryDiff => [Arc<DdlTheoryExpr> => D, Arc<DdlTheoryExpr> => D];
            DdlTheoryExpr::DdlTheoryJoin => [Arc<DdlTheoryExpr> => D, Arc<DdlTheoryExpr> => D];
            DdlTheoryExpr::DdlTheoryMeet => [Arc<DdlTheoryExpr> => D, Arc<DdlTheoryExpr> => D];
            DdlTheoryExpr::DdlTheoryEmpty => [];
            DdlTheoryExpr::DdlTheoryFree => [Arc<DdlPath> => D];
            DdlTheoryExpr::DdlTheoryRef => [Arc<DdlPath> => D];
            DdlTheoryExpr::DdlTheoryLet => [String => Opaque, Arc<DdlTheoryExpr> => D, Arc<DdlTheoryExpr> => D];
            DdlTheoryExpr::DdlTheoryBraceGroup => [Arc<DdlTheoryExpr> => D];
            DdlTheoryExpr::DdlTheoryParenGroup => [Arc<DdlTheoryExpr> => D];
            DdlTheoryExpr::DdlTheoryApply => [Arc<DdlPath> => D, Vec<DdlTheoryExpr> => D];
            DdlTheoryExpr::DdlTheoryTypes => [Arc<DdlTheoryExpr> => D, Vec<DdlCatDecl> => D];
            DdlTheoryExpr::DdlTheoryExports => [Arc<DdlTheoryExpr> => D, Vec<DdlExport> => D];
            DdlTheoryExpr::DdlTheoryReplacements => [Arc<DdlTheoryExpr> => D, Vec<DdlReplacement> => D];
            DdlTheoryExpr::DdlTheoryTerms => [Arc<DdlTheoryExpr> => D, Vec<DdlTermRule> => D];
            DdlTheoryExpr::DdlTheoryEquations => [Arc<DdlTheoryExpr> => D, Vec<DdlEquation> => D];
            DdlTheoryExpr::DdlTheoryRewrites => [Arc<DdlTheoryExpr> => D, Vec<DdlRewrite> => D];
            DdlTheoryExpr::DdlTheoryData => [Arc<DdlTheoryExpr> => D, Arc<Proc> => T];
            DdlTheoryExpr::DdlTheoryTypesImplicit => [Vec<DdlCatDecl> => D];
            DdlTheoryExpr::DdlTheoryExportsImplicit => [Vec<DdlExport> => D];
            DdlTheoryExpr::DdlTheoryReplacementsImplicit => [Vec<DdlReplacement> => D];
            DdlTheoryExpr::DdlTheoryTermsImplicit => [Vec<DdlTermRule> => D];
            DdlTheoryExpr::DdlTheoryEquationsImplicit => [Vec<DdlEquation> => D];
            DdlTheoryExpr::DdlTheoryRewritesImplicit => [Vec<DdlRewrite> => D];
            DdlTheoryExpr::DdlTheoryDataImplicit => [Arc<Proc> => T];
            DdlCatDecl::DdlCategory => [String => Opaque];
            DdlExport::DdlExportDirect => [String => Opaque];
            DdlExport::DdlExportRename => [String => Opaque, String => Opaque];
            DdlReplacement::DdlReplacementRule => [String => Opaque, Arc<DdlTermRule> => D];
            DdlTermRule::DdlTerm => [String => Opaque, Vec<DdlBinding> => D, Vec<DdlSyntaxItem> => D, String => Opaque];
            DdlBinding::DdlBindingPlain => [String => Opaque, Arc<DdlSort> => D];
            DdlBinding::DdlBindingBinder => [String => Opaque, String => Opaque, String => Opaque, String => Opaque];
            DdlSort::DdlSortHashBag => [String => Opaque];
            DdlSort::DdlSortSet => [String => Opaque];
            DdlSort::DdlSortList => [String => Opaque];
            DdlSort::DdlSortCategory => [String => Opaque];
            DdlSyntaxItem::DdlSyntaxProjection => [String => Opaque, String => Opaque];
            DdlSyntaxItem::DdlSyntaxTerminal => [String => Opaque];
            DdlSyntaxItem::DdlSyntaxArgument => [String => Opaque];
            DdlEquation::DdlEquationDirect => [Arc<DdlRuleAst> => D, Arc<DdlRuleAst> => D];
            DdlEquation::DdlEquationConditional => [Arc<DdlFreshnesses> => D, Arc<DdlRuleAst> => D, Arc<DdlRuleAst> => D];
            DdlFreshnesses::DdlFreshnessOne => [Arc<DdlFreshness> => D];
            DdlFreshnesses::DdlFreshnessMore => [Arc<DdlFreshness> => D, Arc<DdlFreshnesses> => D];
            DdlFreshness::DdlFreshness => [String => Opaque, String => Opaque];
            DdlRewrite::DdlRewriteDirect => [String => Opaque, Arc<DdlRuleAst> => D, Arc<DdlRuleAst> => D];
            DdlRewrite::DdlRewriteConditional => [String => Opaque, Arc<DdlPremises> => D, Arc<DdlRuleAst> => D, Arc<DdlRuleAst> => D];
            DdlPremises::DdlPremiseOne => [Arc<DdlPremise> => D];
            DdlPremises::DdlPremiseMore => [Arc<DdlPremise> => D, Arc<DdlPremises> => D];
            DdlPremise::DdlPremise => [String => Opaque, String => Opaque];
            DdlRuleAst::DdlRuleAstSubst => [Arc<DdlRuleAst> => D, Arc<DdlRuleAst> => D];
            DdlRuleAst::DdlRuleAstSExp => [String => Opaque, Vec<DdlRuleAst> => D];
            DdlRuleAst::DdlRuleAstAbs => [String => Opaque, Arc<DdlRuleAst> => D];
            DdlRuleAst::DdlRuleAstCollectionEmpty => [];
            DdlRuleAst::DdlRuleAstRemainderOnly => [String => Opaque];
            DdlRuleAst::DdlRuleAstVar => [String => Opaque];
            DdlRuleAst::DdlRuleAstCollection => [Arc<DdlRuleAstItems> => D];
            DdlRuleAst::DdlRuleAstCollectionRemainder => [Arc<DdlRuleAst> => D, Arc<DdlRuleAstRemainderTail> => D];
            DdlRuleAstItems::DdlRuleAstItemOne => [Arc<DdlRuleAst> => D];
            DdlRuleAstItems::DdlRuleAstItemMore => [Arc<DdlRuleAst> => D, Arc<DdlRuleAstItems> => D];
            DdlRuleAstRemainderTail::DdlRuleAstTailRemainder => [String => Opaque];
            DdlRuleAstRemainderTail::DdlRuleAstTailMore => [Arc<DdlRuleAst> => D, Arc<DdlRuleAstRemainderTail> => D];
        }
    };
}

pub(crate) use rholang_source_profile_rows;
