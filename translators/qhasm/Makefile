OCAMLMAKEFILE = OCamlMakefile
OCAMLC = ocamlc
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
OCAMLFIND = ocamlfind
OCAMLLIBPATH = 
TAGS = otags
TAGSFLAGS =
NCSUFFIX = .native
BCSUFFIX = .byte
PP=camlp4o pa_macro.cmo
export PP
OCAML_VERSION = $(shell ocamlc -version)
OCAML_MAJOR = $(shell ocamlc -version | cut -c1)
OCAML_MINOR = $(shell ocamlc -version | cut -c3-4)
PPFLAGS =
ifeq ($(OCAML_MAJOR), 4)
        PPFLAGS += -DOCAML4
endif
#HAS_SET_OF_LIST = $(shell [[ $(OCAML_MAJOR) -ge 4 && $(OCAML_MINOR) -ge 2 ]] && echo true)
HAS_SET_OF_LIST=true
ifeq ($(HAS_SET_OF_LIST), "true")
	PPFLAGS += -DHAS_SET_OF_LIST
endif

SOURCES = \
	qhasm.ml \
	annotParser.mly annotLexer.mll \
	qhasmParser.mly qhasmLexer.mll \
	generator.ml \
	parser.ml main.ml
MLSOURCES = $(filter %.ml, $(SOURCES))
INTERFACES = $(filter-out main.mli, $(addsuffix .mli, $(basename $(MLSOURCES))))
EXAMPLEDIR = examples
EXAMPLES = $(wildcard $(EXAMPLEDIR)/*.q)
EXAMPLEFLAGS = -c consts
INCDIRS =
LIBDIRS =
MODULES = 
LIBS =
PACKS = num str unix
OCAMLFLAGS = -g
LDFLAGS = -fexceptions
YFLAGS = -v
#CLIBS = stdc++ 
RESULT = qm

all: nc

tags:
	$(TAGS) $(TAGSFLAGS) $(MLSOURCES) $(INTERFACES)

examples: nc $(EXAMPLES)
	@for ex in $(EXAMPLES); do \
		echo Processing $$ex; \
		./$(RESULT)$(NCSUFFIX) $(EXAMPLEFLAGS) $$ex 1> /dev/null; \
	done

distclean:: clean
	rm vc/*.btor vc/*.smt2 vc/*.stp vc/*.cvc3

-include $(OCAMLMAKEFILE)

.PHONY: examples tags
