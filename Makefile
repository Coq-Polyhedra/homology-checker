DUNE ?= dune
COQC ?= coqc
COQMAKEFILE ?= coq_makefile

# Permanent Rocq sources, excluding generated/extraction entry points.
ROCQ_VFILES := $(filter-out \
	src/CheckCert.v \
	src/ExtractChecker.v, \
	$(wildcard src/*.v))

ROCQ_VOFILES := $(ROCQ_VFILES:.v=.vo)

.DEFAULT_GOAL := all

.PHONY: all rocq extract check-cert test clean distclean

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

check-cert: Makefile.coq src/CheckCert.v
	$(MAKE) -f Makefile.coq src/CheckCert.vo

clean:
	@if [ -f Makefile.coq ]; then \
		$(MAKE) -f Makefile.coq clean; \
	fi
	rm -f src/CheckCert.vo
	rm -f src/CheckCert.vos
	rm -f src/CheckCert.vok
	rm -f src/CheckCert.glob
	rm -f ocaml/extracted_checker.ml*
	$(DUNE) clean

distclean: clean
	rm -f Makefile.coq Makefile.coq.conf