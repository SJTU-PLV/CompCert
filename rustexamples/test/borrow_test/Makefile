# all .rs files
SRCS=$(wildcard *.rs)

# Files whose comilation is expected to be failed
FAIL_EXPECTED := 01.rs 03.rs 11.rs 12.rs 13.rs 15.rs 16.rs 17.rs 18.rs 22dangle.rs 32.rs 34.rs

CCOMP=../../../ccomp
CCOMP_FLAGS=-S

# default target
all: test

%.s: %.rs
	$(CCOMP) $(CCOMP_FLAGS) $*.rs

test: $(SRCS)
	@echo "Running tests..."
	@for f in $^; do \
		out=$$($(CCOMP) $(CCOMP_FLAGS) $$f 2>/dev/null; echo $$?); \
		if echo "$(FAIL_EXPECTED)" | grep -q "$$f"; then \
			if [ $$out -ne 0 ]; then \
				printf "PASS (expected failure): %s\n" "$$f"; \
			else \
				printf "FAIL (unexpected success): %s\n" "$$f"; \
			fi; \
		else \
			if [ $$out -eq 0 ]; then \
				printf "PASS (success): %s\n" "$$f"; \
			else \
				printf "FAIL (compile error): %s\n" "$$f"; \
			fi; \
		fi; \
	done

clean:
	rm -f *.s	