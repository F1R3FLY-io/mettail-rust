# Makefile for active Prattail runtime WPDA Rocq proofs.

FORMAL_CAPPED_TARGET_HINT := rocq-prattail-wpda
include ../../capped.mk

CoqMakefile: _CoqProject
	coq_makefile -f $< -o $@

ifneq ($(filter clean,$(MAKECMDGOALS)),clean)
-include CoqMakefile
endif

clean::
	@if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	rm -f CoqMakefile CoqMakefile.conf .CoqMakefile.d theories/.*.aux

.PHONY: clean
