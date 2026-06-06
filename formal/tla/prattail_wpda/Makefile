APALACHE ?= apalache-mc
TLA := PrattailWpda.tla
LENGTH ?= 4
REPO_ROOT := ../../..
LOCAL_TMPDIR ?= $(abspath $(REPO_ROOT)/.formal-tmp)
TMPDIR ?= $(LOCAL_TMPDIR)
export TMPDIR

FORMAL_CAPPED_TARGET_HINT := tla-prattail-wpda
FORMAL_CLEAN_GOALS := clean
include ../../capped.mk

.PHONY: check check-cohort check-chain check-crosscat expected-fail clean prepare-tmp

check: prepare-tmp check-cohort check-chain check-crosscat

prepare-tmp:
	mkdir -p "$(TMPDIR)"

check-cohort: prepare-tmp
	$(APALACHE) --features=no-rows check --length=$(LENGTH) --config=CohortQuotient.cfg $(TLA)

check-chain: prepare-tmp
	$(APALACHE) --features=no-rows check --length=$(LENGTH) --config=ChainAbsorb.cfg $(TLA)

check-crosscat: prepare-tmp
	$(APALACHE) --features=no-rows check --length=$(LENGTH) --config=CrossCat.cfg $(TLA)

expected-fail: prepare-tmp
	@out=$$(mktemp "$$TMPDIR/wrap-sensitive.XXXXXX"); \
	if $(APALACHE) --features=no-rows check --length=$(LENGTH) --config=WrapSensitiveExpectedFail.cfg $(TLA) > "$$out" 2>&1; then \
		cat "$$out"; \
		rm -f "$$out"; \
		echo "expected a wrap-sensitive quotient counterexample, but Apalache reported success"; \
		exit 1; \
	elif grep -q "state invariant 1 violated" "$$out"; then \
		cat "$$out"; \
		rm -f "$$out"; \
		echo "observed expected wrap-sensitive quotient counterexample"; \
	else \
		cat "$$out"; \
		rm -f "$$out"; \
		echo "expected a wrap-sensitive quotient counterexample, but Apalache failed for another reason"; \
		exit 1; \
	fi

clean:
	rm -rf _apalache-out
