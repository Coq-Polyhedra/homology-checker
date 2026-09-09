DUNE ?= dune
COQC ?= coqc
COQMAKEFILE ?= coq_makefile

# Permanent Rocq sources, excluding generated/extraction entry points.
ROCQ_VFILES := $(filter-out \
	src/ExtractChecker.v \
	src/Proofs.v, \
	$(wildcard src/*.v))

ROCQ_VOFILES := $(ROCQ_VFILES:.v=.vo)

.DEFAULT_GOAL := all

.PHONY: all rocq extract test clean distclean

all: rocq extract
	$(DUNE) build --profile release ocaml/homology_checker.exe

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o Makefile.coq

rocq: Makefile.coq
	$(MAKE) -f Makefile.coq $(ROCQ_VOFILES)

extract: Makefile.coq rocq src/ExtractChecker.v
	$(MAKE) -f Makefile.coq src/ExtractChecker.vo
	@if [ ! -f ocaml/extracted_checker.ml ]; then \
		rm -f src/ExtractChecker.vo; \
		$(MAKE) -f Makefile.coq src/ExtractChecker.vo; \
	fi

clean:
	@if [ -f Makefile.coq ]; then \
		$(MAKE) -f Makefile.coq clean; \
	fi
	rm -f ocaml/extracted_checker.ml*
	$(DUNE) clean

distclean: clean
	rm -f Makefile.coq Makefile.coq.conf