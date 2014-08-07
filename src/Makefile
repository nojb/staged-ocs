#
# Build system for ocs library and interpreter
#

include Makefile.common

BC_OBJS = ocs_error.cmo ocs_port.cmo ocs_vartable.cmo ocs_sym.cmo \
	ocs_env.cmo ocs_char.cmo ocs_complex.cmo ocs_numaux.cmo \
	ocs_num.cmo ocs_numstr.cmo ocs_lex.cmo ocs_misc.cmo ocs_read.cmo \
	ocs_stage.cmo ocs_compile.cmo ocs_contin.cmo ocs_print.cmo \
	ocs_io.cmo ocs_list.cmo ocs_macro.cmo ocs_prim.cmo ocs_string.cmo \
	ocs_vector.cmo ocs_wrap.cmo ocs_top.cmo

BCI_OBJS = ocs_main.cmo
BCI = staged_ocscm

all: $(BCI)

$(BCI): $(BC_OBJS) $(BCI_OBJS)
	$(OCAMLC) $(OCAMLFLAGS) -o $(BCI) nums.cma unix.cma $(BC_OBJS) $(BCI_OBJS)

clean:
	-rm -f $(BC_OBJS) $(BCI) *.cm* *.o
	-rm -f $(BCI)

depend:
	$(OCAMLDEP) *.ml *.mli > .depend

include .depend

