PYTHON ?= python3
TERMS ?= 100
PDFLATEX ?= pdflatex

.PHONY: help check paper setup lean baseline complete harness-tests package clean

help:
	@echo "make check  - run exact finite checks (TERMS=100 by default)"
	@echo "make paper  - build build/hanna_congruences.pdf"
	@echo "make lean   - build the pinned Lean project after setup"
	@echo "make setup  - fetch locked dependencies and the required Mathlib cache"
	@echo "make baseline - rebuild and audit the checked foundations"
	@echo "make complete - rebuild and check all 16 final endpoints"
	@echo "make harness-tests - test the axiom-report checker"
	@echo "make package - create and verify the public source ZIP"
	@echo "make clean  - remove the generated build/ directory"

check:
	$(PYTHON) scripts/verify_hanna_congruences.py --terms $(TERMS)

paper:
	mkdir -p build
	@if command -v $(PDFLATEX) >/dev/null 2>&1; then \
		$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory=build manuscript/hanna_congruences.tex && \
		$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory=build manuscript/hanna_congruences.tex; \
	elif command -v tectonic >/dev/null 2>&1; then \
		tectonic --keep-logs --outdir build manuscript/hanna_congruences.tex && \
		tectonic --keep-logs --outdir build manuscript/hanna_congruences.tex; \
	else \
		echo "Install pdflatex or tectonic to build the manuscript." >&2; exit 1; \
	fi

lean:
	cd lean && lake build
	cd lean && lake env lean Audit.lean

setup:
	$(PYTHON) scripts/setup_lean.py

baseline:
	$(PYTHON) scripts/check_formalization.py --mode baseline

complete:
	$(PYTHON) scripts/check_formalization.py --mode complete

harness-tests:
	$(PYTHON) -m unittest discover -s tests -p 'test_*.py'

package:
	$(PYTHON) scripts/package_public.py

clean:
	rm -rf build
