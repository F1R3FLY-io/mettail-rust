APALACHE ?= apalache-mc
TLC ?= tlc
PYTHON ?= python3
GENERATOR ?= ../../process/rho_comm_slice.py
TLA := RhoNetScheduler.tla
LENGTH ?= 4
REPO_ROOT := ../../..
LOCAL_TMPDIR ?= $(abspath $(REPO_ROOT)/.formal-tmp)
TMPDIR ?= $(LOCAL_TMPDIR)
export TMPDIR

FORMAL_CAPPED_TARGET_HINT := tla-rho-machine
FORMAL_CLEAN_GOALS := clean
include ../../capped.mk

.PHONY: check check-generated check-safety check-liveness clean prepare-tmp

check: check-generated prepare-tmp check-safety check-liveness

check-generated:
	$(PYTHON) "$(GENERATOR)" --check

prepare-tmp:
	mkdir -p "$(TMPDIR)"

check-safety: prepare-tmp
	$(APALACHE) --features=no-rows check --length=$(LENGTH) --config=Safety.cfg $(TLA)

check-liveness: prepare-tmp
	$(TLC) -cleanup -workers 1 -config Liveness.cfg $(TLA)

clean:
	rm -rf _apalache-out states RhoNetScheduler.tla.toolbox
