DIRS=utils sitpn hvhdl

COQINCLUDES=$(foreach d, $(DIRS), -R $(d) hilecop.$(d))

COQCOPTS ?= -w -undeclared-scope
COQC=coqc -q $(COQINCLUDES) $(COQCOPTS)

## Compilation files ##

# General-purpose utilities (in utils/)

UTILSFILES=NatMap.v NatSet.v Coqlib.v \
	FstSplit.v InAndNoDup.v ListsPlus.v \
	Arrays.v \

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

HVHDLFILES=ArcT.v TransitionT.v GlobalTypes.v AbstractSyntax.v SemanticalDomains.v \
	Environment.v StaticExpressions.v IsOfType.v DefaultValue.v \
	ExpressionEvaluation.v ConstraintElaboration.v TypeElaboration.v \
	GenericElaboration.v PortElaboration.v ArchitectureElaboration.v \
	ValidSS.v ValidPortMap.v DesignElaboration.v \
	SSEvaluation.v PortMapEvaluation.v CombinationalEvaluation.v \
	SynchronousEvaluation.v Stabilize.v Initialization.v

# Builds files with prefixes

UTILS=$(foreach f, $(UTILSFILES), utils/$f)
SITPN=$(foreach f, $(SITPNFILES), sitpn/$f)
HVHDL=$(foreach f, $(HVHDLFILES), hvhdl/$f)

# All source files

FILES=$(UTILS) $(SITPN) $(HVHDL)

all: proof 

proof: $(FILES:.v=.vo)

utils: $(UTILS:.v=.vo)
sitpn: $(SITPN:.v=.vo)
hvhdl: $(HVHDL:.v=.vo)

%.vo : %.v	
	@echo "COQC $*.v"
	@$(COQC) $*.v  

cleansitpn:
	rm -f $(patsubst %, %/*.vo, sitpn)
	rm -f $(patsubst %, %/.*.aux, sitpn)
	rm -f $(patsubst %, %/*.glob, sitpn)
	rm -f $(patsubst %, %/*.vok, sitpn)
	rm -f $(patsubst %, %/*.vos, sitpn)
	rm -f $(patsubst %, %/*~, sitpn)

cleanhvdl:
	rm -f $(patsubst %, %/*.vo, hvhdl)
	rm -f $(patsubst %, %/.*.aux, hvhdl)
	rm -f $(patsubst %, %/*.glob, hvhdl)
	rm -f $(patsubst %, %/*.vok, hvhdl)
	rm -f $(patsubst %, %/*.vos, hvhdl)
	rm -f $(patsubst %, %/*~, hvhdl)

cleanall:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f $(patsubst %, %/.*.aux, $(DIRS))
	rm -f $(patsubst %, %/*.glob, $(DIRS))
	rm -f $(patsubst %, %/*.vok, $(DIRS))
	rm -f $(patsubst %, %/*.vos, $(DIRS))
	rm -f $(patsubst %, %/*~, $(DIRS))	
