SHELL := /bin/sh

BUILD_DIR ?= .build
PYTHON ?= python3
GENERATOR ?= ../../process/rho_comm_slice.py
MCRL22LPS ?= mcrl22lps
LPS2LTS ?= lps2lts
LPS2PBES ?= lps2pbes
LPS2PBES_FLAGS ?= --preprocess-modal-operators
PBES2BOOL ?= pbes2bool
LTSCOMPARE ?= ltscompare
MCRL2_TAU ?= $(shell $(PYTHON) "$(GENERATOR)" --mcrl2-tau)

FORMAL_CAPPED_TARGET_HINT := mcrl2-rho-machine
FORMAL_CLEAN_GOALS := clean
include ../../capped.mk

.PHONY: check clean check-generated check-rho-formulas check-dovetail-formulas compare

check: check-generated check-rho-formulas check-dovetail-formulas compare

check-generated:
	$(PYTHON) "$(GENERATOR)" --check

$(BUILD_DIR):
	mkdir -p "$(BUILD_DIR)"

$(BUILD_DIR)/rho_net_comm.lps: rho_net_comm.mcrl2 | $(BUILD_DIR)
	$(MCRL22LPS) $< $@

$(BUILD_DIR)/dovetail_fact_steps.lps: dovetail_fact_steps.mcrl2 | $(BUILD_DIR)
	$(MCRL22LPS) $< $@

$(BUILD_DIR)/rho_net_comm.aut: $(BUILD_DIR)/rho_net_comm.lps
	$(LPS2LTS) --out=aut $< $@

$(BUILD_DIR)/dovetail_fact_steps.aut: $(BUILD_DIR)/dovetail_fact_steps.lps
	$(LPS2LTS) --out=aut $< $@

$(BUILD_DIR)/rho_no_deadlock.pbes: $(BUILD_DIR)/rho_net_comm.lps formulas/no_deadlock.mcf
	$(LPS2PBES) $(LPS2PBES_FLAGS) --formula=formulas/no_deadlock.mcf $< $@

$(BUILD_DIR)/rho_internal_schedules.pbes: $(BUILD_DIR)/rho_net_comm.lps formulas/rho_internal_schedules_complete.mcf
	$(LPS2PBES) $(LPS2PBES_FLAGS) --formula=formulas/rho_internal_schedules_complete.mcf $< $@

$(BUILD_DIR)/dovetail_no_deadlock.pbes: $(BUILD_DIR)/dovetail_fact_steps.lps formulas/no_deadlock.mcf
	$(LPS2PBES) $(LPS2PBES_FLAGS) --formula=formulas/no_deadlock.mcf $< $@

$(BUILD_DIR)/dovetail_direct_schedules.pbes: $(BUILD_DIR)/dovetail_fact_steps.lps formulas/dovetail_direct_schedules_complete.mcf
	$(LPS2PBES) $(LPS2PBES_FLAGS) --formula=formulas/dovetail_direct_schedules_complete.mcf $< $@

check-rho-formulas: $(BUILD_DIR)/rho_no_deadlock.pbes $(BUILD_DIR)/rho_internal_schedules.pbes
	@test "$$($(PBES2BOOL) $(BUILD_DIR)/rho_no_deadlock.pbes)" = "true"
	@test "$$($(PBES2BOOL) $(BUILD_DIR)/rho_internal_schedules.pbes)" = "true"

check-dovetail-formulas: $(BUILD_DIR)/dovetail_no_deadlock.pbes $(BUILD_DIR)/dovetail_direct_schedules.pbes
	@test "$$($(PBES2BOOL) $(BUILD_DIR)/dovetail_no_deadlock.pbes)" = "true"
	@test "$$($(PBES2BOOL) $(BUILD_DIR)/dovetail_direct_schedules.pbes)" = "true"

compare: $(BUILD_DIR)/rho_net_comm.aut $(BUILD_DIR)/dovetail_fact_steps.aut
	@test "$$($(LTSCOMPARE) --equivalence=branching-bisim --tau=$(MCRL2_TAU) $^)" = "true"

clean:
	rm -rf "$(BUILD_DIR)"
