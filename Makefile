.PHONY: deps

all:
	dune test


watch:
	dune test -w

deps:
	opam install ppx_variants_conv zlist --yes
