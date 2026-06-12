# Makefile for the Dovetail engine Rocq proofs.
#
# Resource-limited build (recommended, from the repository root):
#   make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-dovetail

FORMAL_CAPPED_TARGET_HINT := rocq-dovetail
include ../../../formal/capped.mk

CoqMakefile: _CoqProject
	coq_makefile -f $< -o $@

-include CoqMakefile

clean::
	@if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	rm -f CoqMakefile CoqMakefile.conf

.PHONY: clean
