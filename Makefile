DUNE ?= dune

.DEFAULT_GOAL := all

.PHONY: all rocq extract test clean

all: extract
	$(DUNE) build --profile release ocaml/homology_checker.exe

rocq:
	$(MAKE) -f Makefile.coq

extract:
	$(MAKE) -f Makefile.coq src/ExtractChecker.vo
	@if [ ! -f ocaml/extracted_checker.ml ]; then \
		rm -f src/ExtractChecker.vo; \
		$(MAKE) -f Makefile.coq src/ExtractChecker.vo; \
	fi

clean:
	$(MAKE) -f Makefile.coq clean
	$(DUNE) clean
	rm -f ocaml/extracted_checker.ml*