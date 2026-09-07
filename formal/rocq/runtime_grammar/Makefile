FORMAL_CAPPED_TARGET_HINT := rocq-runtime-grammar
include ../../capped.mk

CoqMakefile: _CoqProject
	coq_makefile -f $< -o $@

ifneq ($(filter clean,$(MAKECMDGOALS)),clean)
-include CoqMakefile
endif

RUNTIME_GRAMMAR_SECURITY_MODULES := \
	RuntimeGrammar.CapabilitySeparation \
	RuntimeGrammar.InstalledLanguageAuthority \
	RuntimeGrammar.TheoremChannel \
	RuntimeGrammar.BoundedAdmissionChecker \
	RuntimeGrammar.RholangTheoremService \
	RuntimeGrammar.RegistryModuleClosure \
	RuntimeGrammar.WpdaDispatchPartition \
	RuntimeGrammar.StructuralTemplate \
	RuntimeGrammar.StructuralConstructMatch \
	RuntimeGrammar.WireAdmission \
	RuntimeGrammar.StringLiteralTransducer \
	RuntimeGrammar.HostCapabilityManifest \
	RuntimeGrammar.ModuleProgramStaging \
	RuntimeGrammar.SelfHostingFixedPoint \
	RuntimeGrammar.LanguageCoreProjection \
	RuntimeGrammar.BackendModuleEncapsulation \
	RuntimeGrammar.TaggedReconstructionDispatch \
	RuntimeGrammar.TaggedReconstructionMachine \
	RuntimeGrammar.TaggedReconstructionFastPaths \
	RuntimeGrammar.TypedCoproductEliminators \
	RuntimeGrammar.TaggedNormalizationMachine \
	RuntimeGrammar.SharedTypedAssemblyKernel \
	RuntimeGrammar.TerminalVariantIdentity \
	RuntimeGrammar.GeneratedSemanticAdapter \
	RuntimeGrammar.NativeReflectionCodec \
	RuntimeGrammar.InstalledFltHeadCodec \
	RuntimeGrammar.InstalledFltTermCodec \
	RuntimeGrammar.FusedOccurrenceExecution \
	RuntimeGrammar.BorrowedOccurrenceExecution \
	RuntimeGrammar.InstalledFltArena \
	RuntimeGrammar.KernelPositionalNativeView \
	RuntimeGrammar.InstalledFltOccurrence \
	RuntimeGrammar.ReflectedParEnvelope \
	RuntimeGrammar.InstalledFltTraversal \
	RuntimeGrammar.ExecutableTheoryCore \
	RuntimeGrammar.ExecutableTheoryImage \
	RuntimeGrammar.CollectionComprehension \
	RuntimeGrammar.SemanticTransitionKernel \
	RuntimeGrammar.InstalledFltGraphProjection \
	RuntimeGrammar.SemanticIntrinsics \
	RuntimeGrammar.SemanticNormalization \
	RuntimeGrammar.RegexGsltSyntax \
	RuntimeGrammar.RegexGsltMatch \
	RuntimeGrammar.RegexGsltSearch \
	RuntimeGrammar.RegexGsltReplace \
	RuntimeGrammar.RegexGsltRules \
	RuntimeGrammar.RegexGsltOracle

all: check-security-kernel

check-security-kernel: $(patsubst RuntimeGrammar.%,theories/%.vo,$(RUNTIME_GRAMMAR_SECURITY_MODULES))
	$(COQCHK) -silent $(COQLIBS_NOML) $(RUNTIME_GRAMMAR_SECURITY_MODULES)

clean::
	@if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	rm -f CoqMakefile CoqMakefile.conf .CoqMakefile.d theories/.*.aux

.PHONY: check-security-kernel clean
