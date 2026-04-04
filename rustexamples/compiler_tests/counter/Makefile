CCOMP=../../../rust_comp

PROGS=main.rs counter.c
OBJ=counter

$(OBJ).rcompcert: $(PROGS)
	$(CCOMP) $^ -o $@

test:
	@if ./$(OBJ).rcompcert | cmp -s - ../Results/$(OBJ); \
           then echo "$(OBJ): passed"; \
           else echo "$(OBJ): FAILED"; exit 2; \
	   fi; \

clean:
	rm -f *.rcompcert *.compcert *.gcc
	rm -f *.compcert.c *.light.c *.parsed.c *.s *.o *.sdump *~ 
	rm rust_compile.log
