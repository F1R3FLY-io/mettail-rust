TLC ?= tlc
TLA := RuntimeGrammar.tla
THEOREM_CHANNEL_TLA := TheoremChannel.tla
INSTALL_LIFECYCLE_TLA := InstallLifecycle.tla
DERIVATION_RANK_TLA := DerivationRank.tla
REPO_ROOT := ../../..
LOCAL_TMPDIR ?= $(abspath $(REPO_ROOT)/.formal-tmp)
TMPDIR ?= $(LOCAL_TMPDIR)
export TMPDIR

FORMAL_CAPPED_TARGET_HINT := tla-runtime-grammar
FORMAL_CLEAN_GOALS := clean
include ../../capped.mk

.PHONY: check check-safety check-liveness check-theorem-channel check-theorem-channel-unsafe check-install-lifecycle check-derivation-rank check-derivation-rank-unsafe clean prepare-tmp

check: prepare-tmp check-safety check-liveness check-theorem-channel check-theorem-channel-unsafe check-install-lifecycle check-derivation-rank check-derivation-rank-unsafe

prepare-tmp:
	mkdir -p "$(TMPDIR)"

check-safety: prepare-tmp
	$(TLC) -cleanup -workers 1 -config Safety.cfg $(TLA)

check-liveness: prepare-tmp
	$(TLC) -cleanup -workers 1 -config Liveness.cfg $(TLA)

check-theorem-channel: prepare-tmp
	$(TLC) -cleanup -workers 1 -config TheoremChannelSafety.cfg $(THEOREM_CHANNEL_TLA)

check-theorem-channel-unsafe: prepare-tmp
	@log="$(TMPDIR)/theorem-channel-unsafe.log"; \
	if $(TLC) -cleanup -workers 1 -config TheoremChannelUnsafe.cfg $(THEOREM_CHANNEL_TLA) >"$$log" 2>&1; then \
		echo "unsafe theorem-channel model unexpectedly satisfied AllCommitsAuthorized"; \
		cat "$$log"; \
		exit 1; \
	fi; \
	grep -q "Invariant AllCommitsAuthorized is violated" "$$log"

check-install-lifecycle: prepare-tmp
	$(TLC) -cleanup -workers 1 -config InstallLifecycleSafety.cfg $(INSTALL_LIFECYCLE_TLA)

check-derivation-rank: prepare-tmp
	$(TLC) -cleanup -workers 1 -config DerivationRankSafety.cfg $(DERIVATION_RANK_TLA)

check-derivation-rank-unsafe: prepare-tmp
	@log="$(TMPDIR)/derivation-rank-unsafe.log"; \
	if $(TLC) -cleanup -workers 1 -config DerivationRankUnsafe.cfg $(DERIVATION_RANK_TLA) >"$$log" 2>&1; then \
		echo "unsafe transition-timing rank unexpectedly satisfied FinalCanonicalRank"; \
		cat "$$log"; \
		exit 1; \
	fi; \
	grep -q "Invariant FinalCanonicalRank is violated" "$$log"

clean:
	rm -rf states RuntimeGrammar.tla.toolbox InstallLifecycle.tla.toolbox DerivationRank.tla.toolbox
