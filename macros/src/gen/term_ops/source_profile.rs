//! Phase-one source-profile correspondence against the actual generated enums.
//!
//! This fixture is not a public gate or a semantic evaluator. Each line names
//! an exact category and constructor, followed by its complete original Rust
//! field sequence. `@` annotates a category child's source role; opaque native
//! fields have no annotation. The existing classifier determines carriers.
//! T = term, N = name, P = receive pattern, PN = name-shaped receive pattern,
//! G = guard, D = declaration, I = inherit, Q = quote (PN -> P, otherwise T),
//! B = Boolean operand (G -> G, otherwise T).
//!
//! Phase two uses RholangSourceImports' hereditary worklist laws with original
//! borrowed occurrences plus these roles. It must separately discharge source
//! association for the generated paid push/pop/collection/reversal template;
//! this census establishes constructor/field correspondence only.
//!
//! Frozen phase-two scheduling/charging recipe (not activated here):
//! - A single Vec retains typed borrowed jobs (original reference and role).
//!   Prepay reserve_binding_parts(3, 2, 0) before Vec/ordinal initialization
//!   and eventual flat Vec disposal. Schedule the root through the same push
//!   rule as every child; aliases are separate occurrences, without cloning.
//! - Before every pop, including the terminal None, prepay (1, 0, 0).
//!   Before matching a popped category/constructor and checking/incrementing
//!   its occurrence ordinal, prepay (3, 1, 0). Use checked_add; overflow fails
//!   closed, retains previous charges, and yields no successful witness.
//!   Refuse an unlisted constructor here, before any payload projection.
//! - Before retaining the current batch-start index, prepay (1, 1, 0).
//!   Before each original child/collection/scope-body projection prepay
//!   (1, 0, 0). Scope::unsafe_body is a safe Rust borrowed accessor here;
//!   binder patterns are metadata, never opened, cloned, or freshened.
//! - Before constructing/pushing each borrowed job prepay (3, 1, 0): one
//!   construction, one push, and one eventual flat disposal. Opaque String,
//!   native scalar and FltNode payloads have no host-child jobs or inspection.
//! - Vec fields: prepay (1, 1, 0) for iterator setup, then (1, 0, 0) before
//!   every next, including None. Map/Bag fields instead call the existing
//!   try_for_each_entry with the same callback; their paid setup/next/native
//!   scan is not charged a second time. The visitor pays the child projection
//!   and push groups above. Append Map key then value; append each Bag key
//!   once even at count zero, in unchanged native representation order.
//! - Append fields and elements in original declaration/representation order,
//!   then reverse ONLY the newly appended batch using the existing paid
//!   reversal template: (3, 2, 0) setup; (1, 0, 0) each guard including the
//!   terminal guard; (6, 1, 0) each endpoint swap. Keep checked_sub/checked_add
//!   exactly as reverse_binding_task_batch. This choice reuses the existing
//!   paid callback scans without a new lifetime-erased iterator mechanism.
//! - A normal refusal discards only flat borrowed jobs using their prepaid
//!   disposal work, with no further fallible reservation or AST Drop. All
//!   numbers denote logical source groups/records, not allocator byte bounds.
//!   reserve_binding_parts checks work+owned_bytes and 4*records+owned_bytes;
//!   its callback is the caller's existing ReflectedCodecBudget::charge.
//!
//! Law association: RholangInitialGraphResources::precharged_action and its
//! cancellation/refusal/no-refund/exact-success laws apply at every group;
//! SourceMapEntryVisit preserves the original pair prefix and paid advances;
//! NativeHashBagEntryVisit preserves original keys/counts and paid sparse
//! scans. PaidTaskBatchReversal::completed_exterior_is_unchanged and
//! lifo_visits_original_batch give the exact children ++ pending pop order
//! required by RholangSourceImports::accepted_step_preserves_every_ordered_child_occurrence.
//! These are existing laws, not a proof of an emitter that does not yet exist.
//! The remaining phase-two obligation is their concrete generated-source
//! association, including first-refusal diagnostics and every reservation cut.

const PROFILE_ROWS: &str = r#"
Proc PZero|POutputNilEmpty|PPersistOutputNilEmpty|MapEmpty
Proc PVar OrdVar
Proc PDrop Arc<Name>@N
Proc PPar HashBag<Proc>@I
Proc PParInfix Arc<Proc>@I Arc<Proc>@I
Proc POutput|PPersistOutput|POutputQuoted Arc<Name>@N Arc<Proc>@T
Proc POutputShort|PPersistOutputShort Arc<Proc>@T Arc<Proc>@T
Proc POutputEmpty|PPersistOutputEmpty|POutputQuotedEmpty Arc<Name>@N
Proc POutput2Plus|PPersistOutput2Plus|POutputQuoted2Plus Arc<Name>@N Arc<Proc>@T Vec<Proc>@T
Proc POutputShortEmpty|PPersistOutputShortEmpty|POutputNil|PPersistOutputNil Arc<Proc>@T
Proc POutputShort2Plus|PPersistOutputShort2Plus Arc<Proc>@T Arc<Proc>@T Vec<Proc>@T
Proc POutputNil2Plus|PPersistOutputNil2Plus Arc<Proc>@T Vec<Proc>@T
Proc PNew Scope<Vec<Binder<String>>,Arc<Proc>>@T
Proc PNewUris Vec<Uri>@I Scope<Vec<Binder<String>>,Arc<Proc>>@T
Proc PForUser Vec<ForRow>@I Arc<Proc>@T
ForRow ForRowSingleNoWhere Arc<InputBind>@I
ForRow ForRowSingleWhere Arc<InputBind>@I Arc<Proc>@G
ForRow ForRowNoWhere Arc<InputBind>@I Vec<InputBind>@I
ForRow ForRowWhere Arc<InputBind>@I Vec<InputBind>@I Arc<Proc>@G
InputBind InputBind|InputBindPersistent Arc<Name>@PN Arc<Name>@N
InputBind InputBindPolyadic|InputBindPersistentPolyadic Arc<Name>@PN Vec<Name>@PN Arc<Name>@N
InputBind InputBindEmpty|InputBindEmptyPersistent Arc<Name>@N
InputBind InputBindQuoted|InputBindQuotedPersistent Arc<Proc>@P Arc<Name>@N
Name NVar OrdVar
Name NQuoteNil
Name NParen Arc<Name>@I
Name NQuote|NQuoteShort Arc<Proc>@Q
Proc CastInt Arc<Int>@I
Proc CastBool Arc<Bool>@I
Proc CastStr Arc<Str>@I
Proc CastList Arc<List>@I
Proc CastMap Arc<Map>@I
Int NumLit i64
Int NegInt Arc<Int>@I
Bool BoolLit bool
Str StringLit String
List ListLit Vec<Proc>@I
Map MapLit HashMapLit<Proc,Proc>@I
Proc MethodCall Arc<Proc>@T String Vec<Proc>@T
Proc Eq|Ne|Lt|Gt|LtEq|GtEq Arc<Proc>@T Arc<Proc>@T
Proc And|Or|Implies Arc<Proc>@B Arc<Proc>@B
Proc Not Arc<Proc>@B
Proc PFlt|PFltFence|PFltBrace Arc<FltNode>
Uri UriText String
Proc DdlModule String Vec<DdlModuleItem>@D
Proc DdlModuleImported Arc<DdlImports>@D String Vec<DdlModuleItem>@D
Proc DdlTheory String Vec<DdlParam>@D Arc<DdlTheoryExpr>@D
DdlModuleItem DdlModuleTheoryItem Arc<DdlTheoryExpr>@D
DdlModuleItem DdlModuleProcItem Arc<Proc>@T
DdlParam DdlParamDecl String Arc<DdlPath>@D
DdlPath DdlPathQualified String Arc<DdlPath>@D
DdlPath DdlPathName String
DdlImports DdlImportsNonEmpty Arc<DdlImport>@D Vec<DdlImport>@D
DdlImport DdlImportModuleAs|DdlImportFromModule String String
DdlTheoryExpr DdlTheoryDiff|DdlTheoryJoin|DdlTheoryMeet Arc<DdlTheoryExpr>@D Arc<DdlTheoryExpr>@D
DdlTheoryExpr DdlTheoryEmpty
DdlTheoryExpr DdlTheoryFree|DdlTheoryRef Arc<DdlPath>@D
DdlTheoryExpr DdlTheoryLet String Arc<DdlTheoryExpr>@D Arc<DdlTheoryExpr>@D
DdlTheoryExpr DdlTheoryBraceGroup|DdlTheoryParenGroup Arc<DdlTheoryExpr>@D
DdlTheoryExpr DdlTheoryApply Arc<DdlPath>@D Vec<DdlTheoryExpr>@D
DdlTheoryExpr DdlTheoryTypes Arc<DdlTheoryExpr>@D Vec<DdlCatDecl>@D
DdlTheoryExpr DdlTheoryExports Arc<DdlTheoryExpr>@D Vec<DdlExport>@D
DdlTheoryExpr DdlTheoryReplacements Arc<DdlTheoryExpr>@D Vec<DdlReplacement>@D
DdlTheoryExpr DdlTheoryTerms Arc<DdlTheoryExpr>@D Vec<DdlTermRule>@D
DdlTheoryExpr DdlTheoryEquations Arc<DdlTheoryExpr>@D Vec<DdlEquation>@D
DdlTheoryExpr DdlTheoryRewrites Arc<DdlTheoryExpr>@D Vec<DdlRewrite>@D
DdlTheoryExpr DdlTheoryData Arc<DdlTheoryExpr>@D Arc<Proc>@T
DdlTheoryExpr DdlTheoryTypesImplicit Vec<DdlCatDecl>@D
DdlTheoryExpr DdlTheoryExportsImplicit Vec<DdlExport>@D
DdlTheoryExpr DdlTheoryReplacementsImplicit Vec<DdlReplacement>@D
DdlTheoryExpr DdlTheoryTermsImplicit Vec<DdlTermRule>@D
DdlTheoryExpr DdlTheoryEquationsImplicit Vec<DdlEquation>@D
DdlTheoryExpr DdlTheoryRewritesImplicit Vec<DdlRewrite>@D
DdlTheoryExpr DdlTheoryDataImplicit Arc<Proc>@T
DdlCatDecl DdlCategory String
DdlExport DdlExportDirect String
DdlExport DdlExportRename String String
DdlReplacement DdlReplacementRule String Arc<DdlTermRule>@D
DdlTermRule DdlTerm String Vec<DdlBinding>@D Vec<DdlSyntaxItem>@D String
DdlBinding DdlBindingPlain String Arc<DdlSort>@D
DdlBinding DdlBindingBinder String String String String
DdlSort DdlSortHashBag|DdlSortSet|DdlSortList|DdlSortCategory String
DdlSyntaxItem DdlSyntaxProjection String String
DdlSyntaxItem DdlSyntaxTerminal|DdlSyntaxArgument String
DdlEquation DdlEquationDirect Arc<DdlRuleAst>@D Arc<DdlRuleAst>@D
DdlEquation DdlEquationConditional Arc<DdlFreshnesses>@D Arc<DdlRuleAst>@D Arc<DdlRuleAst>@D
DdlFreshnesses DdlFreshnessOne Arc<DdlFreshness>@D
DdlFreshnesses DdlFreshnessMore Arc<DdlFreshness>@D Arc<DdlFreshnesses>@D
DdlFreshness DdlFreshness String String
DdlRewrite DdlRewriteDirect String Arc<DdlRuleAst>@D Arc<DdlRuleAst>@D
DdlRewrite DdlRewriteConditional String Arc<DdlPremises>@D Arc<DdlRuleAst>@D Arc<DdlRuleAst>@D
DdlPremises DdlPremiseOne Arc<DdlPremise>@D
DdlPremises DdlPremiseMore Arc<DdlPremise>@D Arc<DdlPremises>@D
DdlPremise DdlPremise String String
DdlRuleAst DdlRuleAstSubst Arc<DdlRuleAst>@D Arc<DdlRuleAst>@D
DdlRuleAst DdlRuleAstSExp String Vec<DdlRuleAst>@D
DdlRuleAst DdlRuleAstAbs String Arc<DdlRuleAst>@D
DdlRuleAst DdlRuleAstCollectionEmpty
DdlRuleAst DdlRuleAstRemainderOnly|DdlRuleAstVar String
DdlRuleAst DdlRuleAstCollection Arc<DdlRuleAstItems>@D
DdlRuleAst DdlRuleAstCollectionRemainder Arc<DdlRuleAst>@D Arc<DdlRuleAstRemainderTail>@D
DdlRuleAstItems DdlRuleAstItemOne Arc<DdlRuleAst>@D
DdlRuleAstItems DdlRuleAstItemMore Arc<DdlRuleAst>@D Arc<DdlRuleAstItems>@D
DdlRuleAstRemainderTail DdlRuleAstTailRemainder String
DdlRuleAstRemainderTail DdlRuleAstTailMore Arc<DdlRuleAst>@D Arc<DdlRuleAstRemainderTail>@D
"#;

#[path = "source_profile_tests.rs"]
mod tests;
