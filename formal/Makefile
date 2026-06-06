SHELL := /bin/sh

REPO_ROOT := ..
FORMAL_TMPDIR ?= $(abspath $(REPO_ROOT)/target/tmp)
TMPDIR ?= $(FORMAL_TMPDIR)
export TMPDIR

FORMAL_TOOL_PATH_PREFIX ?= $(HOME)/.opam/default/bin:$(HOME)/.elan/bin:$(HOME)/.local/tlaps/bin:$(HOME)/.npm-global/bin:$(HOME)/.cargo/bin
PATH := $(FORMAL_TOOL_PATH_PREFIX):$(PATH)
export PATH

LAKE ?= $(HOME)/.elan/bin/lake
SYSTEMD_RUN ?= systemd-run
FORMAL_MEMORY_HARD_MAX_BYTES := 34359738368
FORMAL_MEMORY_MAX_BYTES ?= 34359738368
FORMAL_MEMORY_HIGH_BYTES ?= 30064771072
FORMAL_TASKS_MAX ?= 128
FORMAL_CAPPED_TARGET ?= check-inner
FORMAL_CARGO_BUILD_JOBS ?= 1
FORMAL_CAPPED_RUN ?= 0

.PHONY: check check-inner check-uncapped check-capped check-memory-cap require-capped clean prepare-tmp
.PHONY: prattail-wpda rocq-support lean-prattail-wpda
.PHONY: tla-prattail-wpda tla-prattail-wpda-expected-fail rust-prattail-wpda
.PHONY: rust-wpda-codegen rust-wpda-generated-smoke
.PHONY: rocq-prattail-wpda rocq-trampoline rocq-advanced-automata
.PHONY: rocq-ascent-optimizations rocq-codegen-optimizations rocq-egraph
.PHONY: rocq-lattice rocq-logict rocq-mathematical-analyses
.PHONY: rocq-predicate-dispatch rocq-presburger rocq-rule-consolidation
.PHONY: rocq-sft rocq-unification lean-prattail-wpda-clean

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
		env PATH="$(PATH)" TMPDIR="$(TMPDIR)" CARGO_BUILD_JOBS="$(FORMAL_CARGO_BUILD_JOBS)" CARGO_INCREMENTAL=0 FORMAL_CAPPED_RUN=1 \
		make -C formal -j1 $(FORMAL_CAPPED_TARGET)

prepare-tmp:
	mkdir -p "$(TMPDIR)"

prattail-wpda: require-capped prepare-tmp rocq-prattail-wpda lean-prattail-wpda tla-prattail-wpda tla-prattail-wpda-expected-fail rust-prattail-wpda rust-wpda-codegen rust-wpda-generated-smoke

rocq-support: require-capped prepare-tmp rocq-trampoline rocq-advanced-automata
rocq-support: rocq-ascent-optimizations rocq-codegen-optimizations
rocq-support: rocq-egraph rocq-lattice rocq-logict rocq-mathematical-analyses
rocq-support: rocq-predicate-dispatch rocq-presburger rocq-rule-consolidation
rocq-support: rocq-sft rocq-unification

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

lean-prattail-wpda: require-capped
	cd lean && $(LAKE) build

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
	$(MAKE) -C rocq/lattice clean
	$(MAKE) -C rocq/logict clean
	$(MAKE) -C rocq/mathematical_analyses clean
	$(MAKE) -C rocq/predicate_dispatch clean
	$(MAKE) -C rocq/presburger clean
	$(MAKE) -C rocq/rule_consolidation clean
	$(MAKE) -C rocq/sft clean
	$(MAKE) -C rocq/unification clean
	$(MAKE) lean-prattail-wpda-clean
	$(MAKE) -C tla/prattail_wpda clean

lean-prattail-wpda-clean:
	cd lean && $(LAKE) clean
