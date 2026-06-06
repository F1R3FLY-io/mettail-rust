FORMAL_CAPPED_RUN ?= 0
FORMAL_CAPPED_TARGET_HINT ?= check-inner
FORMAL_CLEAN_GOALS ?= clean cleanall archclean

ifeq ($(FORMAL_CAPPED_RUN),0)
ifeq ($(MAKECMDGOALS),)
$(error Refusing direct formal verification target; use make -C formal check-capped FORMAL_CAPPED_TARGET=$(FORMAL_CAPPED_TARGET_HINT))
endif
ifneq ($(filter-out $(FORMAL_CLEAN_GOALS),$(MAKECMDGOALS)),)
$(error Refusing direct formal verification target; use make -C formal check-capped FORMAL_CAPPED_TARGET=$(FORMAL_CAPPED_TARGET_HINT))
endif
endif
