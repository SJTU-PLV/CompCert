# all .rs files in subdirectories
SRCS := $(shell find . -type f -name '*.rs' | sed 's|^\./||' | sort)

# Files whose compilation is expected to fail.
FAIL_EXPECTED := ./subtyping/amf-transitive_failure.rs ./subtyping/amf-undeclared_relation.rs ./subtyping/po-missing_bound.rs
FAIL_SRCS := $(FAIL_EXPECTED)

SUCCESS_EXPECTED := $(filter-out $(FAIL_SRCS),$(SRCS))

CCOMP=../../../rust_comp
CCOMP_ABS := $(abspath $(CCOMP))
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

# default target
all: $(SUCCESS_EXPECTED:%.rs=%.compcert)

dump: $(if $(filter-out dump,$(MAKECMDGOALS)),,$(SUCCESS_EXPECTED:%.rs=%.compcert))
	@:

%.s: %.rs
	$(CCOMP) $(CCOMP_ASM_FLAGS) $< -o $@

%.compcert: %.rs
	$(CCOMP) $(CCOM_EXE_FLAGS) $< -o $@

test: $(SRCS)
	@echo "Running standard tests..."
	@for f in $^; do \
		dir=$$(dirname $$f); \
		base=$$(basename $$f); \
		out=$$((cd $$dir && $(CCOMP_ABS) $(CCOMP_ASM_FLAGS) $$base 2>/dev/null); echo $$?); \
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

clean:
	find . -type f \( -name '*.s' -o -name '*.compcert' \
	  -o -name '*.rustsyntax' -o -name '*.rustlight' -o -name '*.rminor' \
	  -o -name '*.rcfg' -o -name '*.init' \
	  -o -name '*.after_elabdrop' -o -name '*.before_borrowck' \
	  -o -name '*.moveck' -o -name '*.borrowck' \
	  -o -name '*.light.c' -o -name '*.compcert.c' -o -name '*.parsed.c' \
	  -o -name '*.cm' -o -name '*.rtl' -o -name '*.alloctrace' \
	  -o -name '*.ltl' -o -name '*.mach' -o -name '*.json' \
	  -o -name '*.o' \) -delete
