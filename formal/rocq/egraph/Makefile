# Makefile for E-Graph Rocq proofs
#
# Usage:
#   make              Build all proofs
#   make clean        Clean build artifacts
#   make CoqMakefile  Regenerate CoqMakefile from _CoqProject
#
# Resource-limited build (recommended, from repository root):
#   make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-egraph

FORMAL_CAPPED_TARGET_HINT := rocq-egraph
include ../../capped.mk

CoqMakefile: _CoqProject
	coq_makefile -f $< -o $@

-include CoqMakefile

clean::
	@if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	rm -f CoqMakefile CoqMakefile.conf

.PHONY: clean
