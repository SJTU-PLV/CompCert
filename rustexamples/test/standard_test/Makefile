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
				 normal/po-vec_push_fail2.rs normal/po-well_formed_function_inputs.rs \
				 normal/rtb-access-permissions.rs normal/rtb-anon-fields-struct.rs normal/rtb-anon-fields-variant.rs \
				 normal/rtb-assign-imm-local-twice.rs normal/rtb-assign-comp.rs normal/rtb-assign-to-andmut-in-aliasable-loc.rs normal/rtb-assign-to-andmut-in-borrowed-loc.rs \
				 normal/rtb-assign-to-immutable-ref.rs normal/rtb-bad-nested-calls-move.rs normal/rtb-borrow-checker-lifetime-error-46471.rs \
				 normal/rtb-borrowck-return.rs normal/rtb-borrowck-uninit.rs normal/rtb-auto-mut-ref-to-immut-var.rs \
				 normal/rtb-bad-nested-calls-free.rs normal/rtb-borrowed-uniq-rvalue.rs normal/rtb-borrow-from-owned-ptr.rs \
				 normal/rtb-borrow-from-stack-variable.rs normal/rtb-borrow-immutable-deref-box.rs normal/rtb-borrow-immut-deref-of-box-as-mut.rs \
				 normal/rtb-borrow-mut-base-ptr-in-aliasable-loc.rs normal/rtb-break-uninit.rs normal/rtb-break-uninit-2.rs \
				 normal/rtb-field-sensitivity-box.rs normal/rtb-for-loop-uninit.rs normal/rtb-if-no-else.rs normal/rtb-if-with-else.rs \
				 normal/rtb-imm-ref-to-mut-rec-field-issue-3162-c.rs normal/rtb-immutable-arg.rs normal/rtb-immut-function-arguments.rs \
				 normal/rtb-init-op-equal.rs normal/rtb-init-plus-equal.rs normal/rtb-issue-14498.rs normal/rtb-issue-2657-1.rs normal/rtb-issue-2657-2.rs \
				 normal/rtb-issue-33819.rs normal/rtb-issue-45199.rs normal/rtb-issue-46471.rs normal/rtb-issue-48962.rs \
				 normal/rtb-issue-52713-bug.rs normal/rtb-issue-92015.rs normal/rtb-lend-flow-if.rs normal/rtb-lend-flow-loop.rs normal/rtb-lend-flow-match.rs \
				 normal/rtb-lend-flow.rs normal/rtb-loan-blocks-move.rs normal/rtb-local-borrow-outlives-fn.rs normal/rtb-match-already-borrowed.rs \
				 normal/rtb-move-from-subpath-of-borrowed-path.rs normal/rtb-move-mut-base-ptr.rs normal/rtb-mut-addr-of-imm-var.rs normal/rtb-mut-borrow-of-mut-base-ptr.rs \
				 normal/rtb-mut-borrow-outside-loop.rs normal/rtb-no-cycle-in-exchange-heap.rs normal/rtb-pat-reassign-binding.rs \
				 normal/rtb-reassignment-immutable-fields-twice.rs normal/rtb-reborrow-from-mut.rs normal/rtb-reborrow-from-shorter-lived-andmut.rs \
				 normal/rtb-reinit.rs normal/rtb-return-ref-to-temporary.rs normal/rtb-storage-dead.rs normal/rtb-swap-mut-base-ptr.rs normal/rtb-tuple-fields.rs \
				 normal/rtb-uninit-after-item.rs normal/rtb-uninit-field-access.rs normal/rtb-uninit-ref-chain.rs normal/rtb-uniq-via-lend.rs \
				 normal/rtb-use-mut-borrow.rs normal/rtb-while-break.rs normal/rtb-while-cond.rs normal/rtb-while.rs normal/rtb-unary-move.rs \
				 normal/rtn-borrowed-local-error.rs normal/rtn-borrowed-match-issue-45045.rs normal/rtn-borrowed-referent-issue-38899.rs \
				 normal/rtn-borrowed-temporary-error.rs normal/rtn-borrowed-universal-error-2.rs normal/rtn-borrowed-universal-error.rs \
				 normal/rtn-guarantor-issue-46974.rs normal/rtn-issue-48803.rs normal/rtn-issue-57989.rs \
				 normal/rtn-loan-ends-mid-block-pair.rs normal/rtn-polonius-return-ref-to-local.rs normal/rtn-polonius-well-formed-inputs.rs \
				 normal/rtn-reference-carried-through-struct-field.rs normal/rtn-region-ends-after-if-condition.rs normal/rtn-return-ref-mut-issue-46557.rs \
				 flow_sensitivity/rtn-issue-46036.rs flow_sensitivity/rtn-polonius-use-while-mut-fr.rs flow_sensitivity/rtn-polonius-use-while-mut.rs \
				 subtyping/rtn-anon-to-static.rs subtyping/rtn-outlives-foo1.rs subtyping/rtn-outlives-foo2.rs subtyping/rtn-outlives-foo3.rs \
				 subtyping/rtn-outlives-foo4.rs subtyping/rtn-subset-missing.rs


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
