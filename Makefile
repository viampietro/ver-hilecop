DIRS=utils sitpn hvhdl

COQINCLUDES=$(foreach d, $(DIRS), -R $(d) hilecop.$(d))

COQCOPTS ?= -w -undeclared-scope
COQC=coqc -q $(COQINCLUDES) $(COQCOPTS)

## Compilation files ##

# General-purpose utilities (in utils/)

UTILSFILES=HilecopDefinitions.v HilecopLemmas.v \
	  HilecopTactics.v HilecopExtraLemmas.v

# Sitpn structures, semantics and token player (in spn/)

SITPNFILES=Sitpn.v SitpnSemantics.v SitpnTokenPlayer.v \
	SitpnTactics.v SitpnCoreLemmas.v SitpnWellDefMarking.v \
	SitpnWellDefFired.v SitpnWellDefInterpretation.v SitpnWellDefTime.v \
	SitpnRisingEdgeMarking.v SitpnFallingEdgeWellDef.v SitpnFallingEdgeFired.v \
	SitpnFallingEdgeInterpretation.v SitpnFallingEdgeTime.v \
	SitpnFallingEdgeCorrect.v SitpnRisingEdgeWellDef.v \
	SitpnRisingEdgeTime.v SitpnRisingEdgeInterpretation.v \
	SitpnRisingEdgeCorrect.v SitpnCorrect.v \
	SitpnFallingEdgeInterpretationComplete.v SitpnFallingEdgeFiredComplete.v \
	SitpnFallingEdgeTimeComplete.v SitpnFallingEdgeComplete.v \
	SitpnRisingEdgeMarkingComplete.v SitpnRisingEdgeTimeComplete.v \
	SitpnRisingEdgeInterpretationComplete.v SitpnRisingEdgeComplete.v \
	SitpnComplete.v \

# H-VHDL syntax and semantics.

HVHDLFILES=Values.v Syntax.v

# Builds files with prefixes

UTILS=$(foreach f, $(UTILSFILES), utils/$f)
SITPN=$(foreach f, $(SITPNFILES), sitpn/$f)
HVHDL=$(foreach f, $(HVHDLFILES), hvhdl/$f)

# All source files

FILES=$(UTILS) $(SITPN) $(HVHDL)

all: proof 

proof: $(FILES:.v=.vo)

%.vo : %.v	
	@echo "COQC $*.v"
	@$(COQC) $*.v  

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f $(patsubst %, %/.*.aux, $(DIRS))
