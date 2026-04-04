CCOMP=../../rust_comp

PROGS=fib factorial list1 list2 list3 list4 elaborate_drop nested_box

all: $(PROGS:%=%.rcompcert)

%.rcompcert: %.rs
	$(CCOMP) $*.rs -o $*.rcompcert

test:
	@for i in $(PROGS); do \
	   if ./$$i.rcompcert | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; exit 2; \
	   fi; \
         done

clean:
	rm -f *.rcompcert *.compcert *.gcc
	rm -f *.compcert.c *.light.c *.parsed.c *.s *.o *.sdump *~
	rm rust_compile.log
