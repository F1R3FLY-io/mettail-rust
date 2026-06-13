TLC ?= tlc
TLA := RhoPurseSettlement.tla
REPO_ROOT := ../../..
LOCAL_TMPDIR ?= $(abspath $(REPO_ROOT)/.formal-tmp)
TMPDIR ?= $(LOCAL_TMPDIR)
export TMPDIR

FORMAL_CAPPED_TARGET_HINT := tla-rho-settlement
FORMAL_CLEAN_GOALS := clean
include ../../capped.mk

.PHONY: check check-safety clean prepare-tmp

check: prepare-tmp check-safety

prepare-tmp:
	mkdir -p "$(TMPDIR)"

check-safety: prepare-tmp
	$(TLC) -cleanup -workers 1 -config Safety.cfg $(TLA)

clean:
	rm -rf states RhoPurseSettlement.tla.toolbox
