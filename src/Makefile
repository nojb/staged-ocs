#
# Build system for ocs library and interpreter
#

OCAMLBUILD = ocamlbuild
METAOCAMLC = metaocamlc

byte:
	@OCAMLFIND_COMMANDS="ocamlc=$(METAOCAMLC)" \
	$(OCAMLBUILD) -classic-display -ocamlc $(METAOCAMLC) -use-ocamlfind -no-links ocs_main.byte

clean:
	ocamlbuild -clean

.PHONY: byte clean
