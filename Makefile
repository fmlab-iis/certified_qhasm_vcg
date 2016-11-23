#############################################################################
##  v      #                   The Coq Proof Assistant                     ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##
##   \VV/  #                                                               ##
##    //   #  Makefile automagically generated by coq_makefile V8.5pl2     ##
#############################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f .project -o Makefile 
#

.DEFAULT_GOAL := all

# This Makefile may take arguments passed as environment variables:
# COQBIN to specify the directory where Coq binaries resides;
# TIMECMD set a command to log .v compilation time;
# TIMED if non empty, use the default time command as TIMECMD;
# ZDEBUG/COQDEBUG to specify debug flags for ocamlc&ocamlopt/coqc;
# DSTROOT to specify a prefix to install path.

# Here is a hack to make $(eval $(shell works:
define donewline


endef
includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

TIMED=
TIMECMD=
STDTIME?=/usr/bin/time -f "$* (user: %U mem: %M ko)"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

vo_to_obj = $(addsuffix .o,\
  $(filter-out Warning: Error:,\
  $(shell $(COQBIN)coqtop -q -noinit -batch -quiet -print-mod-uid $(1))))

##########################
#                        #
# Libraries definitions. #
#                        #
##########################

COQLIBS?=\
  -Q "lib/CompCert" CompCert\
  -Q "lib/gbarith/src" GBArith\
  -Q "common" Common\
  -Q "qhasm" Qhasm\
  -Q "sqhasm" sQhasm\
  -Q "mqhasm" mQhasm\
  -I "."
COQCHKLIBS?=\
  -R "lib/CompCert" CompCert\
  -R "lib/gbarith/src" GBArith\
  -R "common" Common\
  -R "qhasm" Qhasm\
  -R "sqhasm" sQhasm\
  -R "mqhasm" mQhasm
COQDOCLIBS?=\
  -R "lib/CompCert" CompCert\
  -R "lib/gbarith/src" GBArith\
  -R "common" Common\
  -R "qhasm" Qhasm\
  -R "sqhasm" sQhasm\
  -R "mqhasm" mQhasm

##########################
#                        #
# Variables definitions. #
#                        #
##########################


OPT?=
COQDEP?="$(COQBIN)coqdep" -c
COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQCHKFLAGS?=-silent -o
COQDOCFLAGS?=-interpolate -utf8
COQC?=$(TIMER) "$(COQBIN)coqc"
GALLINA?="$(COQBIN)gallina"
COQDOC?="$(COQBIN)coqdoc"
COQCHK?="$(COQBIN)coqchk"
COQMKTOP?="$(COQBIN)coqmktop"

##################
#                #
# Install Paths. #
#                #
##################

ifdef USERINSTALL
XDG_DATA_HOME?="$(HOME)/.local/share"
COQLIBINSTALL=$(XDG_DATA_HOME)/coq
COQDOCINSTALL=$(XDG_DATA_HOME)/doc/coq
else
COQLIBINSTALL="${COQLIB}user-contrib"
COQDOCINSTALL="${DOCDIR}user-contrib"
COQTOPINSTALL="${COQLIB}toploop"
endif

######################
#                    #
# Files dispatching. #
#                    #
######################

VFILES:=lib/CompCert/Coqlib.v\
  lib/CompCert/Integers.v\
  common/Notations.v\
  common/Tactics.v\
  common/Arch.v\
  common/Types.v\
  common/Lists.v\
  common/FMaps.v\
  common/FSets.v\
  common/Bools.v\
  common/Nats.v\
  common/ZAriths.v\
  common/Bits.v\
  common/Integers.v\
  common/HList.v\
  common/Var.v\
  common/Env.v\
  common/Store.v\
  qhasm/IProg.v\
  qhasm/MiniQhasmPlusAMD64.v\
  qhasm/IProgGenAMD64.v\
  sqhasm/IProg.v\
  sqhasm/MiniQhasmPlusAMD64.v\
  mqhasm/mQhasm.v\
  mqhasm/SSA.v\
  mqhasm/PolyGen.v\
  mqhasm/Radix.v\
  mqhasm/Verify.v

ifneq ($(filter-out archclean clean cleanall printenv,$(MAKECMDGOALS)),)
-include $(addsuffix .d,$(VFILES))
else
ifeq ($(MAKECMDGOALS),)
-include $(addsuffix .d,$(VFILES))
endif
endif

.SECONDARY: $(addsuffix .d,$(VFILES))

VO=vo
VOFILES:=$(VFILES:.v=.$(VO))
VOFILES1=$(patsubst lib/CompCert/%,%,$(filter lib/CompCert/%,$(VOFILES)))
VOFILES3=$(patsubst common/%,%,$(filter common/%,$(VOFILES)))
VOFILES4=$(patsubst qhasm/%,%,$(filter qhasm/%,$(VOFILES)))
VOFILES5=$(patsubst sqhasm/%,%,$(filter sqhasm/%,$(VOFILES)))
VOFILES6=$(patsubst mqhasm/%,%,$(filter mqhasm/%,$(VOFILES)))
GLOBFILES:=$(VFILES:.v=.glob)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)
OBJFILES=$(call vo_to_obj,$(VOFILES))
ALLNATIVEFILES=$(OBJFILES:.o=.cmi) $(OBJFILES:.o=.cmo) $(OBJFILES:.o=.cmx) $(OBJFILES:.o=.cmxs)
NATIVEFILES=$(foreach f, $(ALLNATIVEFILES), $(wildcard $f))
NATIVEFILES1=$(patsubst lib/CompCert/%,%,$(filter lib/CompCert/%,$(NATIVEFILES)))
NATIVEFILES3=$(patsubst common/%,%,$(filter common/%,$(NATIVEFILES)))
NATIVEFILES4=$(patsubst qhasm/%,%,$(filter qhasm/%,$(NATIVEFILES)))
NATIVEFILES5=$(patsubst sqhasm/%,%,$(filter sqhasm/%,$(NATIVEFILES)))
NATIVEFILES6=$(patsubst mqhasm/%,%,$(filter mqhasm/%,$(NATIVEFILES)))
ifeq '$(HASNATDYNLINK)' 'true'
HASNATDYNLINK_OR_EMPTY := yes
else
HASNATDYNLINK_OR_EMPTY :=
endif

#######################################
#                                     #
# Definition of the toplevel targets. #
#                                     #
#######################################

all: $(VOFILES) 

quick: $(VOFILES:.vo=.vio)

vio2vo:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio2vo $(J) $(VOFILES:%.vo=%.vio)
checkproofs:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio-checking $(J) $(VOFILES:%.vo=%.vio)
gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d html $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html -g $(COQDOCLIBS) -d html $(VFILES)

all.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

validate: $(VOFILES)
	$(COQCHK) $(COQCHKFLAGS) $(COQCHKLIBS) $(notdir $(^:.vo=))

beautify: $(VFILES:=.beautified)
	for file in $^; do mv $${file%.beautified} $${file%beautified}old && mv $${file} $${file%.beautified}; done
	@echo 'Do not do "make clean" until you are sure that everything went well!'
	@echo 'If there were a problem, execute "for file in $$(find . -name \*.v.old -print); do mv $${file} $${file%.old}; done" in your shell/'

.PHONY: all archclean beautify byte clean cleanall gallina gallinahtml html install install-doc install-natdynlink install-toploop opt printenv quick uninstall userinstall validate vio2vo

####################
#                  #
# Special targets. #
#                  #
####################

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

userinstall:
	+$(MAKE) USERINSTALL=true install

install:
	cd "mqhasm" && for i in $(NATIVEFILES6) $(GLOBFILES6) $(VFILES6) $(VOFILES6); do \
	 install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/mQhasm/$$i`"; \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/mQhasm/$$i; \
	done
	cd "sqhasm" && for i in $(NATIVEFILES5) $(GLOBFILES5) $(VFILES5) $(VOFILES5); do \
	 install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/sQhasm/$$i`"; \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/sQhasm/$$i; \
	done
	cd "qhasm" && for i in $(NATIVEFILES4) $(GLOBFILES4) $(VFILES4) $(VOFILES4); do \
	 install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/Qhasm/$$i`"; \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Qhasm/$$i; \
	done
	cd "common" && for i in $(NATIVEFILES3) $(GLOBFILES3) $(VFILES3) $(VOFILES3); do \
	 install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/Common/$$i`"; \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Common/$$i; \
	done
	cd "lib/CompCert" && for i in $(NATIVEFILES1) $(GLOBFILES1) $(VFILES1) $(VOFILES1); do \
	 install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/CompCert/$$i`"; \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/CompCert/$$i; \
	done

install-doc:
	install -d "$(DSTROOT)"$(COQDOCINSTALL)/$(INSTALLDEFAULTROOT)/html
	for i in html/*; do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQDOCINSTALL)/$(INSTALLDEFAULTROOT)/$$i;\
	done

uninstall_me.sh: Makefile
	echo '#!/bin/sh' > $@
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/mQhasm && rm -f $(NATIVEFILES6) $(GLOBFILES6) $(VFILES6) $(VOFILES6) && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "mQhasm" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/sQhasm && rm -f $(NATIVEFILES5) $(GLOBFILES5) $(VFILES5) $(VOFILES5) && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "sQhasm" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Qhasm && rm -f $(NATIVEFILES4) $(GLOBFILES4) $(VFILES4) $(VOFILES4) && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Qhasm" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/Common && rm -f $(NATIVEFILES3) $(GLOBFILES3) $(VFILES3) $(VOFILES3) && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "Common" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/GBArith && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "GBArith" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/CompCert && rm -f $(NATIVEFILES1) $(GLOBFILES1) $(VFILES1) $(VOFILES1) && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "CompCert" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL)/$(INSTALLDEFAULTROOT) \\\n' >> "$@"
	printf '&& rm -f $(shell find "html" -maxdepth 1 -and -type f -print)\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL) && find $(INSTALLDEFAULTROOT)/html -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	chmod +x $@

uninstall: uninstall_me.sh
	sh $<

.merlin:
	@echo 'FLG -rectypes' > .merlin
	@echo "B $(COQLIB) kernel" >> .merlin
	@echo "B $(COQLIB) lib" >> .merlin
	@echo "B $(COQLIB) library" >> .merlin
	@echo "B $(COQLIB) parsing" >> .merlin
	@echo "B $(COQLIB) pretyping" >> .merlin
	@echo "B $(COQLIB) interp" >> .merlin
	@echo "B $(COQLIB) printing" >> .merlin
	@echo "B $(COQLIB) intf" >> .merlin
	@echo "B $(COQLIB) proofs" >> .merlin
	@echo "B $(COQLIB) tactics" >> .merlin
	@echo "B $(COQLIB) tools" >> .merlin
	@echo "B $(COQLIB) toplevel" >> .merlin
	@echo "B $(COQLIB) stm" >> .merlin
	@echo "B $(COQLIB) grammar" >> .merlin
	@echo "B $(COQLIB) config" >> .merlin
	@echo "B /Users/mht208/.git/certified_qhasm_vcg" >> .merlin
	@echo "S /Users/mht208/.git/certified_qhasm_vcg" >> .merlin

clean::
	rm -f $(OBJFILES) $(OBJFILES:.o=.native) $(NATIVEFILES)
	find . -name .coq-native -type d -empty -delete
	rm -f $(VOFILES) $(VOFILES:.vo=.vio) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	- rm -rf html mlihtml uninstall_me.sh

cleanall:: clean
	rm -f $(patsubst %.v,.%.aux,$(VFILES))

archclean::
	rm -f *.cmx *.o

printenv:
	@"$(COQBIN)coqtop" -config
	@echo 'CAMLC =	$(CAMLC)'
	@echo 'CAMLOPTC =	$(CAMLOPTC)'
	@echo 'PP =	$(PP)'
	@echo 'COQFLAGS =	$(COQFLAGS)'
	@echo 'COQLIBINSTALL =	$(COQLIBINSTALL)'
	@echo 'COQDOCINSTALL =	$(COQDOCINSTALL)'

Makefile: .project
	mv -f $@ $@.bak
	"$(COQBIN)coq_makefile" -f $< -o $@


###################
#                 #
# Implicit rules. #
#                 #
###################

$(VOFILES): %.vo: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $<

$(GLOBFILES): %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $<

$(VFILES:.v=.vio): %.vio: %.v
	$(COQC) -quick $(COQDEBUG) $(COQFLAGS) $<

$(GFILES): %.g: %.v
	$(GALLINA) $<

$(VFILES:.v=.tex): %.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex $< -o $@

$(HTMLFILES): %.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS) -html $< -o $@

$(VFILES:.v=.g.tex): %.g.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex -g $< -o $@

$(GHTMLFILES): %.g.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS)  -html -g $< -o $@

$(addsuffix .d,$(VFILES)): %.v.d: %.v
	$(COQDEP) $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

$(addsuffix .beautified,$(VFILES)): %.v.beautified:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -beautify $*.v

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

