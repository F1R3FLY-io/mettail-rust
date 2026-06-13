SHELL := /bin/sh

BUILD_DIR ?= .build
PYTHON ?= python3
GENERATOR ?= ../../process/rho_comm_slice.py
MAUDE ?= maude
MAUDE_LIB ?= /usr/share/maude
export MAUDE_LIB

FORMAL_CAPPED_TARGET_HINT := maude-rho-machine
FORMAL_CLEAN_GOALS := clean
include ../../capped.mk

.PHONY: check clean check-generated

check: check-generated $(BUILD_DIR)/comm-schedule.log
	$(PYTHON) "$(GENERATOR)" --check-maude-log "$(BUILD_DIR)/comm-schedule.log"

check-generated:
	$(PYTHON) "$(GENERATOR)" --check

$(BUILD_DIR):
	mkdir -p "$(BUILD_DIR)"

$(BUILD_DIR)/comm-schedule.log: rho-net.maude dovetail-rules.maude checks/comm-schedule.maude $(GENERATOR) ../../process/rho_comm_slice.json | $(BUILD_DIR)
	cd checks && $(MAUDE) -no-banner comm-schedule.maude > "../$@"

clean:
	rm -rf "$(BUILD_DIR)"
