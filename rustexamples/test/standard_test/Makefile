# all .rs files in subdirectories
SRCS := $(shell find . -type f -name '*.rs' | sed 's|^\./||' | sort)

# Files whose compilation is expected to fail.
FAIL_EXPECTED := drop_move/amf-break_drops_borrowed_local.rs drop_move/amf-continue_drops_borrowed_local_loop_carried.rs \
				 drop_move/amf-drop_on_break_while_borrowed.rs drop_move/amf-drop_while_borrowed.rs drop_move/amf-drop_while_mutably_borrowed.rs \
				 drop_move/amf-move_in_loop.rs drop_move/amf-move_out_of_borrowed_place.rs drop_move/amf-move_out_of_mut_ref.rs drop_move/amf-move_out_of_shared_ref.rs \
				 drop_move/amf-move_parent_then_access_child.rs drop_move/amf-move_same_field_twice.rs drop_move/amf-move_whole_then_access_field.rs \
				 drop_move/amf-partial_move_use_whole.rs drop_move/amf-use_of_moved_variable.rs \
				 drop_move/po-drop_prevents_mutation.rs \
				 subtyping/amf-transitive_failure.rs subtyping/amf-undeclared_relation.rs subtyping/po-missing_bound.rs subtyping/amf-undeclared_relation_no_return.rs \
				 normal/amf-call_mut_under_shared_borrow.rs normal/amf-loan_cannot_outlive_lifetime_fail.rs normal/amf-mutable_ref_prevents_mutation.rs \
				 normal/amf-shared_ref_prevents_mutation.rs normal/amf-struct_conflicting_field_borrows.rs normal/amf-struct_construction_with_borrowed_local.rs \
				 normal/amf-struct_with_mutable_reference_locks_local.rs normal/amf-uninitialized_return.rs normal/amf-use_of_uninitialized_variable.rs \
				 normal/amf-write_to_borrowed_before_continue.rs normal/amf-write_to_borrowed_before_zero_iteration_loop.rs normal/po-conditional_init.rs \
				 normal/po-return_ref_to_local.rs normal/po-use_while_mut.rs normal/po-use_while_mut_fr.rs normal/po-vec_push_fail1.rs \
				 normal/po-vec_push_fail2.rs normal/po-well_formed_function_inputs.rs

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
		out=$$( (cd $$dir && $(CCOMP_ABS) $(CCOMP_ASM_FLAGS) $$base 2>/dev/null); echo $$?); \
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
