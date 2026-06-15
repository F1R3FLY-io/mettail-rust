# Makefile for the symbolic-algebra Rocq proofs.
#
# Resource-limited build (recommended, from repository root):
#   make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-symbolic-algebra

FORMAL_CAPPED_TARGET_HINT := rocq-symbolic-algebra
include ../../capped.mk

CoqMakefile: _CoqProject
	coq_makefile -f $< -o $@

-include CoqMakefile

clean::
	@if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	rm -f CoqMakefile CoqMakefile.conf

.PHONY: clean
