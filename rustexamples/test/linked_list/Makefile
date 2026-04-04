CCOMP=../../../rust_comp

PROGS=linked_list.rs printer.c
OBJ=linked_list

$(OBJ).compcert: $(PROGS)
	$(CCOMP) $^ -o $@ -drust_all

# test:
# 	@if ./$(OBJ).rcompcert | cmp -s - ../Results/$(OBJ); \
#            then echo "$(OBJ): passed"; \
#            else echo "$(OBJ): FAILED"; exit 2; \
# 	   fi; \

clean:
	rm -f *.s *.compcert
	rm -f *.rustsyntax *.rustlight *.rminor *.rcfg *.init
	rm -f *.after_elabdrop *.before_borrowck *.moveck *.borrowck
	rm -f *.light.c *.compcert.c *.parsed.c *.cm *.rtl *.alloctrace *.ltl *.mach *.json
	rm -f *.o
