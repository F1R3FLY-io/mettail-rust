SHELL := /bin/sh

REPO_ROOT := ..
FORMAL_TMPDIR ?= $(abspath $(REPO_ROOT)/.formal-tmp)
TMPDIR ?= $(FORMAL_TMPDIR)
export TMPDIR

FORMAL_TOOL_PATH_PREFIX ?= $(HOME)/.opam/default/bin:$(HOME)/.local/tlaps/bin:$(HOME)/.npm-global/bin:$(HOME)/.cargo/bin
PATH := $(FORMAL_TOOL_PATH_PREFIX):$(PATH)
export PATH

SYSTEMD_RUN ?= systemd-run
FORMAL_MEMORY_HARD_MAX_BYTES := 34359738368
FORMAL_MEMORY_MAX_BYTES ?= 34359738368
FORMAL_MEMORY_HIGH_BYTES ?= 30064771072
FORMAL_TASKS_MAX ?= 128
FORMAL_CAPPED_TARGET ?= check-inner
FORMAL_CARGO_BUILD_JOBS ?= 1
FORMAL_CARGO_TARGET_DIR ?= $(FORMAL_TMPDIR)/cargo-target
FORMAL_CAPPED_RUN ?= 0
CREUSOT_TOOLCHAIN ?= nightly-2026-04-21
CREUSOT_CARGO ?= $(HOME)/.local/opt/creusot/target/release/cargo-creusot
CREUSOT_RUSTC ?= $(HOME)/.local/bin/creusot-rustc
CREUSOT_PACKAGE_SRC ?= $(HOME)/.local/opt/creusot/target/creusot/packages
CREUSOT_DATA_HOME ?= $(FORMAL_TMPDIR)/creusot-data
CREUSOT_XDG_CONFIG_HOME ?= $(FORMAL_TMPDIR)/xdg-config

.PHONY: check check-inner check-uncapped check-capped check-memory-cap require-capped clean prepare-tmp
.PHONY: prattail-wpda rocq-support
.PHONY: tla-prattail-wpda tla-prattail-wpda-expected-fail rust-prattail-wpda
.PHONY: rust-wpda-codegen rust-wpda-generated-smoke
.PHONY: rocq-prattail-wpda rocq-trampoline rocq-advanced-automata
.PHONY: rocq-ascent-optimizations rocq-codegen-optimizations rocq-egraph rocq-dovetail rocq-dovetail-refinement rocq-dovetail-requirements rocq-critical-zero-admission rocq-rho-bridge rocq-rho-bridge-delta1 rocq-rho-bridge-delta1-matching rocq-rho-bridge-flip-gate rocq-rho-bridge-lowering-boundary rocq-rho-bridge-schedule-family
.PHONY: rocq-lattice rocq-logict rocq-mathematical-analyses
.PHONY: rocq-predicate-dispatch rocq-presburger rocq-rule-consolidation
.PHONY: rocq-sft rocq-unification
.PHONY: process-rho-generated-check process-rho-comm-slice process-rho-first-slice mcrl2-rho-machine maude-rho-machine tla-rho-machine tla-rho-settlement
.PHONY: why3-dovetail-budget creusot-dovetail-budget prepare-creusot-data

check: check-capped

check-inner: require-capped
	mkdir -p "$(TMPDIR)"
	$(MAKE) prattail-wpda
	$(MAKE) rocq-support

check-uncapped:
	@echo "Refusing uncapped formal verification; use check-capped so RSS stays within the 32 GiB hard cap."
	@exit 2

require-capped:
	@if [ "$(FORMAL_CAPPED_RUN)" != "1" ]; then \
		echo "Refusing direct formal verification target; use check-capped so RSS stays within the 32 GiB hard cap."; \
		exit 2; \
	fi

check-memory-cap:
	@max='$(FORMAL_MEMORY_MAX_BYTES)'; \
	high='$(FORMAL_MEMORY_HIGH_BYTES)'; \
	hard='$(FORMAL_MEMORY_HARD_MAX_BYTES)'; \
	case "$$max" in ''|*[!0-9]*) \
		echo "FORMAL_MEMORY_MAX_BYTES must be an integer byte count"; exit 2;; \
	esac; \
	case "$$high" in ''|*[!0-9]*) \
		echo "FORMAL_MEMORY_HIGH_BYTES must be an integer byte count"; exit 2;; \
	esac; \
	if [ "$$max" -gt "$$hard" ]; then \
		echo "FORMAL_MEMORY_MAX_BYTES=$$max exceeds hard cap $$hard bytes (32 GiB)"; exit 2; \
	fi; \
	if [ "$$high" -gt "$$max" ]; then \
		echo "FORMAL_MEMORY_HIGH_BYTES=$$high exceeds FORMAL_MEMORY_MAX_BYTES=$$max"; exit 2; \
	fi

check-capped: check-memory-cap
	mkdir -p "$(TMPDIR)"
	command -v "$(SYSTEMD_RUN)" >/dev/null
	$(SYSTEMD_RUN) --user --pipe --wait --collect \
		-p MemoryAccounting=yes \
		-p MemoryMax=$(FORMAL_MEMORY_MAX_BYTES) \
		-p MemoryHigh=$(FORMAL_MEMORY_HIGH_BYTES) \
		-p MemorySwapMax=0 \
		-p TasksMax=$(FORMAL_TASKS_MAX) \
		--working-directory="$(abspath $(REPO_ROOT))" \
		env PATH="$(PATH)" TMPDIR="$(TMPDIR)" CARGO_TARGET_DIR="$(FORMAL_CARGO_TARGET_DIR)" CARGO_BUILD_JOBS="$(FORMAL_CARGO_BUILD_JOBS)" CARGO_INCREMENTAL=0 FORMAL_CAPPED_RUN=1 \
		make -C formal -j1 $(FORMAL_CAPPED_TARGET)

prepare-tmp:
	mkdir -p "$(TMPDIR)"

prattail-wpda: require-capped prepare-tmp rocq-prattail-wpda tla-prattail-wpda tla-prattail-wpda-expected-fail rust-prattail-wpda rust-wpda-codegen rust-wpda-generated-smoke

rocq-support: require-capped prepare-tmp rocq-trampoline rocq-advanced-automata
rocq-support: rocq-ascent-optimizations rocq-codegen-optimizations
rocq-support: rocq-dovetail rocq-rho-bridge rocq-egraph rocq-lattice rocq-logict rocq-mathematical-analyses
rocq-support: rocq-predicate-dispatch rocq-presburger rocq-rule-consolidation
rocq-support: rocq-sft rocq-unification rocq-critical-zero-admission

rocq-prattail-wpda: require-capped
	$(MAKE) -C rocq/prattail_wpda_runtime

rocq-trampoline: require-capped
	$(MAKE) -C rocq/trampoline

rocq-advanced-automata: require-capped
	$(MAKE) -C rocq/advanced_automata

rocq-ascent-optimizations: require-capped
	$(MAKE) -C rocq/ascent_optimizations

rocq-codegen-optimizations: require-capped
	$(MAKE) -C rocq/codegen_optimizations

rocq-egraph: require-capped
	$(MAKE) -C rocq/egraph

rocq-dovetail: require-capped
	$(MAKE) -C ../dovetail/formal/rocq

rocq-dovetail-refinement: require-capped
	$(MAKE) -C ../dovetail/formal/rocq theories/Refinement/RhoReportHandoff.vo
	$(MAKE) -C ../dovetail/formal/rocq theories/Refinement/RustModelBridge.vo
	$(MAKE) -C ../dovetail/formal/rocq theories/Rigail/NewtonSccAdequacy.vo

rocq-dovetail-requirements: require-capped
	$(MAKE) -C ../dovetail/formal/rocq theories/Requirements/MeTTaILRewriteCoverage.vo
	$(MAKE) -C ../dovetail/formal/rocq theories/Requirements/LanguageDefInventory.vo
	$(MAKE) -C ../dovetail/formal/rocq theories/Lowering/PatternLoweringSoundness.vo

rocq-critical-zero-admission: require-capped
	python3 scripts/check_rocq_zero_admission.py --self-test
	python3 scripts/check_rocq_zero_admission.py

rocq-dovetail-cyclic-boundary: require-capped
	$(MAKE) -C ../dovetail/formal/rocq theories/Extraction/CyclicEnumerationImpossibility.vo
	$(MAKE) -C ../dovetail/formal/rocq theories/Extraction/ExtractionOutcome.vo

rocq-rho-bridge: require-capped
	$(MAKE) -C rocq/rho_bridge

rocq-rho-bridge-artifact-boundary: require-capped
	$(MAKE) -C rocq/rho_bridge theories/RhoArtifactBoundary.vo

rocq-rho-bridge-rejected-coverage: require-capped
	$(MAKE) -C rocq/rho_bridge theories/RhoRejectedCoverage.vo

rocq-rho-bridge-lowering-boundary: require-capped
	$(MAKE) -C rocq/rho_bridge theories/RhoLoweringTotalOrRejects.vo
	$(MAKE) -C rocq/rho_bridge theories/RhoParWellFormedness.vo
	$(MAKE) -C rocq/rho_bridge theories/RhoArtifactBoundary.vo
	$(MAKE) -C rocq/rho_bridge theories/RhoAstSendBoundary.vo
	$(MAKE) -C rocq/rho_bridge theories/RhocalcAstLowering.vo

rocq-rho-bridge-schedule-family: require-capped
	$(MAKE) -C rocq/rho_bridge theories/RhoCommScheduleFamily.vo

rocq-rho-bridge-cbn-budget: require-capped
	$(MAKE) -C rocq/rho_bridge theories/RhoCallByNeedBudget.vo

rocq-rho-bridge-delta1: require-capped
	$(MAKE) -C rocq/rho_bridge theories/DeltaOneMinCostJoin.vo
	$(MAKE) -C rocq/rho_bridge theories/DeltaOneMinCostMatching.vo

rocq-rho-bridge-delta1-matching: rocq-rho-bridge-delta1

rocq-rho-bridge-escrow-settlement: require-capped
	$(MAKE) -C rocq/rho_bridge theories/RhoEscrowSettlement.vo

rocq-rho-bridge-purse-determinism: require-capped
	$(MAKE) -C rocq/rho_bridge theories/RhoPurseDeterminism.vo

rocq-rho-bridge-flip-gate: require-capped
	$(MAKE) -C rocq/rho_bridge theories/RhoBackendFlipGate.vo
	$(MAKE) -C rocq/rho_bridge theories/RhoRejectedCoverage.vo
	$(MAKE) -C rocq/rho_bridge theories/RhoPlannedExecutionBoundary.vo
	$(MAKE) -C rocq/rho_bridge theories/RhoArtifactBoundary.vo
	$(MAKE) -C rocq/rho_bridge theories/RhoObservationReportBoundary.vo
	$(MAKE) -C rocq/rho_bridge theories/RuntimeBackendDispatch.vo

process-rho-generated-check: require-capped
	python3 process/rho_comm_slice.py --self-test
	python3 process/rho_comm_slice.py --check

mcrl2-rho-machine: require-capped
	$(MAKE) -C mcrl2/rho_machine check

maude-rho-machine: require-capped
	$(MAKE) -C maude/rho_machine check

tla-rho-machine: require-capped
	$(MAKE) -C tla/rho_machine check

tla-rho-settlement: require-capped
	$(MAKE) -C tla/rho_settlement check

process-rho-comm-slice: require-capped process-rho-generated-check mcrl2-rho-machine maude-rho-machine tla-rho-machine

process-rho-first-slice: process-rho-comm-slice

why3-dovetail-budget: require-capped
	why3 prove -P "Alt-Ergo,2.6.0" -t 5 ../dovetail/formal/why3/key_budget_contract.mlw

prepare-creusot-data: require-capped prepare-tmp
	CREUSOT_DATA_HOME="$(abspath $(CREUSOT_DATA_HOME))" \
	CREUSOT_PACKAGE_SRC="$(CREUSOT_PACKAGE_SRC)" \
	sh ../dovetail/formal/creusot/prepare-creusot-data.sh

creusot-dovetail-budget: require-capped prepare-creusot-data
	cd ../dovetail/formal/creusot && \
		CREUSOT_DATA_HOME="$(abspath $(CREUSOT_DATA_HOME))" \
		XDG_CONFIG_HOME="$(abspath $(CREUSOT_XDG_CONFIG_HOME))" \
		CARGO_TARGET_DIR="$(abspath $(FORMAL_CARGO_TARGET_DIR))/creusot-dovetail" \
		rustup run "$(CREUSOT_TOOLCHAIN)" "$(CREUSOT_CARGO)" creusot why3-conf
	cd ../dovetail/formal/creusot && \
		CREUSOT_DATA_HOME="$(abspath $(CREUSOT_DATA_HOME))" \
		XDG_CONFIG_HOME="$(abspath $(CREUSOT_XDG_CONFIG_HOME))" \
		CARGO_TARGET_DIR="$(abspath $(FORMAL_CARGO_TARGET_DIR))/creusot-dovetail" \
		rustup run "$(CREUSOT_TOOLCHAIN)" "$(CREUSOT_CARGO)" creusot --only=coma --span-mode=off --creusot-rustc "$(CREUSOT_RUSTC)"
	cd ../dovetail/formal/creusot && \
		PATH="$(abspath $(CREUSOT_DATA_HOME))/bin:$(PATH)" \
		DUNE_DIR_LOCATIONS="why3find:lib:$(abspath $(CREUSOT_DATA_HOME))/share/why3find" \
		WHY3CONFIG="$(abspath $(CREUSOT_XDG_CONFIG_HOME))/creusot/why3.conf" \
		why3find prove --no-autodetect-provers --package creusot --fast 0.2 --time 1 --depth 6 \
			--prover alt-ergo,z3,cvc4 --tactic compute_specified,split_vc \
			--why3-warn-off unused_variable,axiom_abstract \
			verif/dovetail_creusot_formal_rlib/try_add_with_budget.coma \
			verif/dovetail_creusot_formal_rlib/added_never_overshoots_budget.coma \
			verif/dovetail_creusot_formal_rlib/overflow_preserves_state_at_limit.coma \
			verif/dovetail_creusot_formal_rlib/add_succeeds_below_limit.coma \
			verif/dovetail_creusot_formal_rlib/admit_enode_with_budget.coma \
			verif/dovetail_creusot_formal_rlib/admission_never_overshoots_budget.coma \
			verif/dovetail_creusot_formal_rlib/existing_enode_preserves_budget_state.coma \
			verif/dovetail_creusot_formal_rlib/fresh_enode_below_limit_adds_once.coma \
			verif/dovetail_creusot_formal_rlib/fresh_enode_at_limit_sets_node_limit.coma

rocq-lattice: require-capped
	$(MAKE) -C rocq/lattice

rocq-logict: require-capped
	$(MAKE) -C rocq/logict

rocq-mathematical-analyses: require-capped
	$(MAKE) -C rocq/mathematical_analyses

rocq-predicate-dispatch: require-capped
	$(MAKE) -C rocq/predicate_dispatch

rocq-presburger: require-capped
	$(MAKE) -C rocq/presburger

rocq-rule-consolidation: require-capped
	$(MAKE) -C rocq/rule_consolidation

rocq-sft: require-capped
	$(MAKE) -C rocq/sft

rocq-unification: require-capped
	$(MAKE) -C rocq/unification

tla-prattail-wpda: require-capped
	$(MAKE) -C tla/prattail_wpda check

tla-prattail-wpda-expected-fail: require-capped
	$(MAKE) -C tla/prattail_wpda expected-fail

rust-prattail-wpda: require-capped
	cd .. && CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS="$(FORMAL_CARGO_BUILD_JOBS)" cargo test -j1 -p mettail-prattail --features walker-stats wpda_walker --lib

rust-wpda-codegen: require-capped
	cd .. && CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS="$(FORMAL_CARGO_BUILD_JOBS)" cargo test -j1 -p mettail-macros wpda_codegen --lib

rust-wpda-generated-smoke: require-capped
	cd .. && CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS="$(FORMAL_CARGO_BUILD_JOBS)" cargo test -j1 -p mettail-languages --test wpda_via_str_smoke calculator_bool_eq_int_cross_cat_infix_via_wpds -- --exact
	cd .. && CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS="$(FORMAL_CARGO_BUILD_JOBS)" cargo test -j1 -p mettail-languages --test class2_opt_collection_smoke choosemaybe_parse_some_via_wpda -- --exact
	cd .. && CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS="$(FORMAL_CARGO_BUILD_JOBS)" cargo test -j1 -p mettail-languages --test wpda_lattice_backend

clean:
	$(MAKE) -C rocq/prattail_wpda_runtime clean
	$(MAKE) -C rocq/trampoline clean
	$(MAKE) -C rocq/advanced_automata clean
	$(MAKE) -C rocq/ascent_optimizations clean
	$(MAKE) -C rocq/codegen_optimizations clean
	$(MAKE) -C rocq/egraph clean
	$(MAKE) -C ../dovetail/formal/rocq clean
	$(MAKE) -C rocq/rho_bridge clean
	$(MAKE) -C mcrl2/rho_machine clean
	$(MAKE) -C maude/rho_machine clean
	$(MAKE) -C tla/rho_machine clean
	$(MAKE) -C rocq/lattice clean
	$(MAKE) -C rocq/logict clean
	$(MAKE) -C rocq/mathematical_analyses clean
	$(MAKE) -C rocq/predicate_dispatch clean
	$(MAKE) -C rocq/presburger clean
	$(MAKE) -C rocq/rule_consolidation clean
	$(MAKE) -C rocq/sft clean
	$(MAKE) -C rocq/unification clean
	$(MAKE) -C tla/prattail_wpda clean
