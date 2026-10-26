# Makefile for the MeTTaIL <-> f1r3node-rust bridge Rocq proofs.
#
# Resource-limited build (recommended, from the repository root):
#   make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-rho-bridge

FORMAL_CAPPED_TARGET_HINT := rocq-rho-bridge
include ../../capped.mk
.DEFAULT_GOAL := all

# This default follows the native workspace paths in the root Cargo.toml.
NATIVE_COST_ACCOUNTED_RHO ?= $(abspath ../../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho)
NATIVE_PREFIX_ROOT_KEY := $(firstword $(shell printf '%s' '$(NATIVE_COST_ACCOUNTED_RHO)' | sha256sum))
NATIVE_PREFIX_CACHE := $(abspath ../../../target/formal/rho_bridge-native/$(NATIVE_PREFIX_ROOT_KEY))
NATIVE_PREFIX_SELECTION := $(abspath ../../../target/formal/rho_bridge-native/selected-root)
NATIVE_PREFIX_SEEDS := NativeFundingSnapshot LocatedAuthoritySettlement LocatedStackConsumption CanonicalCustodyAliasing OrderedStackMaterialization StagedGuestFundingObligations NativeOperationJournal CausalStackOrder CostMonad CACategory WrappingSubjectReduction CAGradedTransition
NATIVE_PREFIX_RELATIVE := $(shell cd '$(NATIVE_COST_ACCOUNTED_RHO)' 2>/dev/null && coqdep -sort -Q theories CostAccountedRho $(addprefix theories/,$(addsuffix .v,$(NATIVE_PREFIX_SEEDS))))
NATIVE_PREFIX_STAGED := $(addprefix $(NATIVE_PREFIX_CACHE)/,$(notdir $(NATIVE_PREFIX_RELATIVE)))

CoqMakefile: _CoqProject Makefile $(NATIVE_PREFIX_SELECTION) $(NATIVE_PREFIX_STAGED)
	@test -n '$(NATIVE_PREFIX_STAGED)' || { printf '%s\n' 'Set NATIVE_COST_ACCOUNTED_RHO to the native formal/rocq/cost_accounted_rho directory.' >&2; exit 1; }
	coq_makefile -f $< -Q '$(NATIVE_PREFIX_CACHE)' CostAccountedRho $(NATIVE_PREFIX_STAGED) -o $@
	rm -f .CoqMakefile.d

$(NATIVE_PREFIX_SELECTION): FORCE
	@mkdir -p '$(dir $(NATIVE_PREFIX_SELECTION))'
	@printf '%s\n' '$(NATIVE_COST_ACCOUNTED_RHO)' | cmp -s - '$@' || printf '%s\n' '$(NATIVE_COST_ACCOUNTED_RHO)' > '$@'

$(NATIVE_PREFIX_CACHE)/%.v: $(NATIVE_COST_ACCOUNTED_RHO)/theories/%.v
	@mkdir -p '$(NATIVE_PREFIX_CACHE)'
	cp '$<' '$@'

all: CoqMakefile
	$(MAKE) -f CoqMakefile all

BRIDGE_FORWARD_GOALS := $(filter-out all clean CoqMakefile,$(MAKECMDGOALS))
ifneq ($(BRIDGE_FORWARD_GOALS),)
$(BRIDGE_FORWARD_GOALS): CoqMakefile
	$(MAKE) -f CoqMakefile $@
endif

clean::
	@if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	rm -f CoqMakefile CoqMakefile.conf

.PHONY: all clean FORCE $(BRIDGE_FORWARD_GOALS)
