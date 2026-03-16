# Makefile for SFT Rocq proofs
#
# Usage:
#   make              Build all proofs
#   make clean        Clean build artifacts
#   make CoqMakefile  Regenerate CoqMakefile from _CoqProject
#
# Resource-limited build (recommended):
#   systemd-run --user --scope -p MemoryMax=126G -p CPUQuota=1800% \
#     -p IOWeight=30 -p TasksMax=200 make -j1

CoqMakefile: _CoqProject
	coq_makefile -f $< -o $@

-include CoqMakefile

clean::
	@if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	rm -f CoqMakefile CoqMakefile.conf

.PHONY: clean
