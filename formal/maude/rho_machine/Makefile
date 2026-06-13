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
	@grep -A8 "RHO-NET-COMM : a b c =>! S:State" "$(BUILD_DIR)/comm-schedule.log" | grep -q "S:State --> completed"
	@grep -A8 "RHO-NET-COMM : a b c =>! S:State" "$(BUILD_DIR)/comm-schedule.log" | grep -q "No more solutions"
	@grep -A8 "DOVETAIL-FACT-STEPS : a b c =>! S:State" "$(BUILD_DIR)/comm-schedule.log" | grep -q "S:State --> completed"
	@grep -A8 "DOVETAIL-FACT-STEPS : a b c =>! S:State" "$(BUILD_DIR)/comm-schedule.log" | grep -q "No more solutions"
	@grep -A4 "RHO-NET-COMM : a b c =>\\* b c reservedA" "$(BUILD_DIR)/comm-schedule.log" | grep -q "Solution 1"
	@grep -A4 "RHO-NET-COMM : a b c =>\\* b c firedA" "$(BUILD_DIR)/comm-schedule.log" | grep -q "Solution 1"
	@grep -A4 "RHO-NET-COMM : a b c =>\\* a c reservedB" "$(BUILD_DIR)/comm-schedule.log" | grep -q "Solution 1"
	@grep -A4 "RHO-NET-COMM : a b c =>\\* a c firedB" "$(BUILD_DIR)/comm-schedule.log" | grep -q "Solution 1"
	@grep -A4 "RHO-NET-COMM : a b c =>\\* a b reservedC" "$(BUILD_DIR)/comm-schedule.log" | grep -q "Solution 1"
	@grep -A4 "RHO-NET-COMM : a b c =>\\* a b firedC" "$(BUILD_DIR)/comm-schedule.log" | grep -q "Solution 1"
	@grep -A4 "RHO-NET-COMM : a b c =>\\* reservedJoin" "$(BUILD_DIR)/comm-schedule.log" | grep -q "Solution 1"
	@grep -A4 "DOVETAIL-FACT-STEPS : a b c =>\\* b c firedA" "$(BUILD_DIR)/comm-schedule.log" | grep -q "Solution 1"
	@grep -A4 "DOVETAIL-FACT-STEPS : a b c =>\\* a c firedB" "$(BUILD_DIR)/comm-schedule.log" | grep -q "Solution 1"
	@grep -A4 "DOVETAIL-FACT-STEPS : a b c =>\\* a b firedC" "$(BUILD_DIR)/comm-schedule.log" | grep -q "Solution 1"

check-generated:
	$(PYTHON) "$(GENERATOR)" --check

$(BUILD_DIR):
	mkdir -p "$(BUILD_DIR)"

$(BUILD_DIR)/comm-schedule.log: rho-net.maude dovetail-rules.maude checks/comm-schedule.maude | $(BUILD_DIR)
	cd checks && $(MAUDE) -no-banner comm-schedule.maude > "../$@"

clean:
	rm -rf "$(BUILD_DIR)"
