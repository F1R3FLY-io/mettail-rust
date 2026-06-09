# Makefile for the MeTTaIL <-> f1r3node-rust bridge Rocq proofs.
#
# Resource-limited build (recommended, from the repository root):
#   make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-rho-bridge

FORMAL_CAPPED_TARGET_HINT := rocq-rho-bridge
include ../../capped.mk

CoqMakefile: _CoqProject
	coq_makefile -f $< -o $@

-include CoqMakefile

clean::
	@if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	rm -f CoqMakefile CoqMakefile.conf

.PHONY: clean
