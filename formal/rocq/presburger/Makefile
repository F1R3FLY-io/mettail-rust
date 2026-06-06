COQMAKEFILE := CoqMakefile
COQMAKEFILEFLAGS := -f _CoqProject

FORMAL_CAPPED_TARGET_HINT := rocq-presburger
include ../../capped.mk

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	coq_makefile $(COQMAKEFILEFLAGS) -o $(COQMAKEFILE)

clean:
	-$(MAKE) -f $(COQMAKEFILE) clean
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

.PHONY: all clean
