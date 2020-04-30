DIRS=common sitpn hvhdl

COQINCLUDES=$(foreach d, $(DIRS), -R $(d) hilecop.$(d))

COQCOPTS ?= -w -undeclared-scope
COQC=coqc -q $(COQINCLUDES) $(COQCOPTS)

## Compilation files ##

# General-purpose utilities (in common/)

COMMONFILES=NatMap.v NatSet.v Coqlib.v GlobalTypes.v \
	FstSplit.v InAndNoDup.v ListsPlus.v ListsDep.v \

# Sitpn structures, semantics and token player (in sitpn/simpl/)

SITPNSIMPLFILES=Sitpn.v SitpnSemantics.v SitpnTokenPlayer.v \
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

# Sitpn structures, semantics and token player (in sitpn/sets/)

SITPNSETSFILES=SitpnTypes.v Sitpn.v SitpnSemantics.v \
	InfosTypes.v GenerateInfos.v

# H-VHDL syntax and semantics.

HVHDLFILES=HVhdlTypes.v AbstractSyntax.v SemanticalDomains.v \
	Environment.v StaticExpressions.v DefaultValue.v \
	ExpressionEvaluation.v ConstraintElaboration.v TypeElaboration.v \
	GenericElaboration.v PortElaboration.v ArchitectureElaboration.v \
	ValidSS.v ValidPortMap.v DesignElaboration.v \
	SSEvaluation.v PortMapEvaluation.v \
	Petri.v \
	CombinationalEvaluation.v SynchronousEvaluation.v Stabilize.v \
	Initialization.v Simulation.v \
	Place.v Transition.v

# Builds files with prefixes

COMMON=$(foreach f, $(COMMONFILES), common/$f)
SITPNSIMPL=$(foreach f, $(SITPNSIMPLFILES), sitpn/simpl/$f)
SITPNSETS=$(foreach f, $(SITPNSETSFILES), sitpn/sets/$f)
HVHDL=$(foreach f, $(HVHDLFILES), hvhdl/$f)

# All source files

FILES=$(COMMON) $(SITPNSIMPL) $(SITPNSETS) $(HVHDL)

all: proof 

proof: $(FILES:.v=.vo)

common: $(COMMON:.v=.vo)
sitpnsimpl: $(SITPNSIMPL:.v=.vo)
sitpnsets: $(SITPNSETS:.v=.vo)
hvhdl: $(HVHDL:.v=.vo)

%.vo : %.v	
	@echo "COQC $*.v"
	@$(COQC) $*.v  

cleansitpn:
	rm -f $(patsubst %, %/*/*.vo, sitpn)
	rm -f $(patsubst %, %/*/.*.aux, sitpn)
	rm -f $(patsubst %, %/*/*.glob, sitpn)
	rm -f $(patsubst %, %/*/*.vok, sitpn)
	rm -f $(patsubst %, %/*/*.vos, sitpn)
	rm -f $(patsubst %, %/*/*~, sitpn)

cleanhvhdl:
	rm -f $(patsubst %, %/*.vo, hvhdl)
	rm -f $(patsubst %, %/.*.aux, hvhdl)
	rm -f $(patsubst %, %/*.glob, hvhdl)
	rm -f $(patsubst %, %/*.vok, hvhdl)
	rm -f $(patsubst %, %/*.vos, hvhdl)
	rm -f $(patsubst %, %/*~, hvhdl)

cleanall:
	rm -f $(patsubst %, %/*/*.vo, $(DIRS))
	rm -f $(patsubst %, %/*/.*.aux, $(DIRS))
	rm -f $(patsubst %, %/*/*.glob, $(DIRS))
	rm -f $(patsubst %, %/*/*.vok, $(DIRS))
	rm -f $(patsubst %, %/*/*.vos, $(DIRS))
	rm -f $(patsubst %, %/*/*~, $(DIRS))	
