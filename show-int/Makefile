# based on hs-to-coq/examples/successors/Makefile

HS_TO_COQ_ROOT = ../hs-to-coq

include $(HS_TO_COQ_ROOT)/common.mk

# Edit this
GENMODS = Simple GhcShow
MANMODS = Proofs

# Abstract stuff

VFILES_GEN = $(addsuffix .v,$(subst .,/,$(GENMODS)))
VFILES_MAN = $(addsuffix .v,$(MANMODS))

VFILES   = $(VFILES_GEN) $(VFILES_MAN)

all: coq

$(VFILES_GEN): %.v : %.hs edits  $(HS_TO_COQ_ROOT)/base/edits
	$(HS_TO_COQ) -e edits -e $(HS_TO_COQ_ROOT)/base/edits --iface-dir $(HS_TO_COQ_ROOT)/base $< -o .

_CoqProject : Makefile
	> $@
	echo '-Q .               ""'		>> $@
	echo "-Q $(HS_TO_COQ_ROOT)/base-thy/ Proofs" >> $@
	echo "-Q $(HS_TO_COQ_ROOT)/base/     \"\""		>> $@
	echo $(VFILES)										>> $@

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq $(VFILES)
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f */*/*.vo */*/*.glob */*/*.v.d */*.vo */*.glob */*.v.d *.glob *.vo *.v.d _CoqProject Makefile.coq $(VFILES_GEN) */*.v~

