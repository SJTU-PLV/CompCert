# all .rs files
SRCS=$(wildcard *.rs)

# Files whose comilation is expected to be failed
FAIL_EXPECTED := 01.rs 03.rs 11.rs 12.rs 13.rs 15.rs 16.rs 17.rs 18.rs 22dangle.rs 32.rs 34.rs 36.rs 41.rs 43_self_ref.rs 48_shr_ref_invariant.rs

# Files whose comilation would be failed. Compared to FAIL_EXPECTED,
# it addtionaly contains 21struct_enum_generic.rs whose syntax is not
# supported now.
FAIL_SRCS := 01.rs 03.rs 11.rs 12.rs 13.rs 15.rs 16.rs 17.rs 18.rs 22dangle.rs 21struct_enum_generic.rs 32.rs 34.rs 36.rs 41.rs 43_self_ref.rs 48_shr_ref_invariant.rs

SUCCESS_EXPECTED := $(filter-out $(FAIL_SRCS),$(SRCS))

CCOMP=../../rust_comp
DUMP_FLAGS :=
ifneq ($(filter dump,$(MAKECMDGOALS)),)
DUMP_FLAGS += -drust_all
endif

CCOMP_ASM_FLAGS=-dclight -S $(DUMP_FLAGS)
CCOM_EXE_FLAGS=-dclight $(DUMP_FLAGS)

GREEN=\033[32m
RED=\033[31m
RESET=\033[0m

.PHONY: all test clean dump
.PHONY: compare-rustc

# default target
all: $(SUCCESS_EXPECTED:%.rs=%.compcert)

dump: $(if $(filter-out dump,$(MAKECMDGOALS)),,$(SUCCESS_EXPECTED:%.rs=%.compcert))
	@:

%.s: %.rs
	$(CCOMP) $(CCOMP_ASM_FLAGS) $< -o $@

%.compcert: %.rs
	$(CCOMP) $(CCOM_EXE_FLAGS) $< -o $@

test: $(SRCS)
	@echo "Running tests..."
	@for f in $^; do \
		out=$$($(CCOMP) $(CCOMP_ASM_FLAGS) $$f 2>/dev/null; echo $$?); \
		if echo "$(FAIL_EXPECTED)" | grep -q "$$f"; then \
			if [ $$out -ne 0 ]; then \
				printf "$(GREEN)PASS$(RESET) (expected failure): %s\n" "$$f"; \
			else \
				printf "$(RED)FAIL$(RESET) (unexpected success): %s\n" "$$f"; \
			fi; \
		else \
			if [ $$out -eq 0 ]; then \
				printf "$(GREEN)PASS$(RESET) (success): %s\n" "$$f"; \
			else \
				printf "$(RED)FAIL$(RESET) (compile error): %s\n" "$$f"; \
			fi; \
		fi; \
	done

compare-rustc:
	python3 compare_rustc_ccomp.py

clean:
	rm -f *.s *.compcert
	rm -f *.rustsyntax *.rustlight *.rminor *.rcfg *.init
	rm -f *.after_elabdrop *.before_borrowck *.moveck *.borrowck
	rm -f *.light.c *.compcert.c *.parsed.c *.cm *.rtl *.alloctrace *.ltl *.mach *.json
	rm -f *.o
