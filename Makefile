DIRS=common sitpn hvhdl sitpn2hvhdl # soundness

COQINCLUDES=$(foreach d, $(DIRS), -R $(d) hilecop.$(d))

COQCOPTS ?= -w -undeclared-scope
COQC=coqc -q $(COQINCLUDES) $(COQCOPTS)

## Compilation files ##

# General-purpose utilities (in common/)

COMMONFILES=NatMap.v NatMapFacts.v NatSet.v NMap.v NSet.v Coqlib.v GlobalTypes.v GlobalFacts.v \
	ListPlusTactics.v FstSplit.v InAndNoDup.v ListsPlus.v ListsDep.v \
	StateAndErrorMonad.v ListsMonad.v

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

# Sitpn structures, semantics and token player (in sitpn/dp/)

SITPNDPFILES=SitpnTypes.v Sitpn.v SitpnFacts.v SitpnWellDefined.v \
	SitpnSemanticsDefs.v Fired.v SitpnSemantics.v \
 

# H-VHDL syntax and semantics.

HVHDLFILES=HVhdlTypes.v AbstractSyntax.v SemanticalDomains.v \
	Environment.v StaticExpressions.v DefaultValue.v \
	ExpressionEvaluation.v ConstraintElaboration.v TypeElaboration.v \
	GenericElaboration.v PortElaboration.v ArchitectureElaboration.v \
	ValidSS.v ValidPortMap.v DesignElaboration.v \
	SSEvaluation.v PortMapEvaluation.v \
	Petri.v \
	CombinationalEvaluation.v SynchronousEvaluation.v Stabilize.v \
	Place.v Transition.v \
	Initialization.v HilecopDesignStore.v Simulation.v \
	Elaboration.v AbstractSyntaxDefs.v \
	WellDefinedDesign.v


# SITPN to H-VHDL transformation.

SITPN2HVHDLFILES= Sitpn2HVhdlTypes.v \
		GenerateInfos.v GenerateArchitecture.v \
		GeneratePorts.v	GenerateHVhdl.v

# Soundness proof, theorems and lemmas.

SOUNDNESSFILES=Soundness.v

# Builds files with prefixes

COMMON=$(foreach f, $(COMMONFILES), common/$f)
SITPNSIMPL=$(foreach f, $(SITPNSIMPLFILES), sitpn/simpl/$f)
SITPNDP=$(foreach f, $(SITPNDPFILES), sitpn/dp/$f)
HVHDL=$(foreach f, $(HVHDLFILES), hvhdl/$f)
SITPN2HVHDL=$(foreach f, $(SITPN2HVHDLFILES), sitpn2hvhdl/$f)
SOUNDNESS=$(foreach f, $(SOUNDNESSFILES), soundness/$f)

# All source files

FILES=$(COMMON) $(SITPNSIMPL) $(SITPNDP) $(HVHDL) $(SITPN2HVHDL)

all: proof 

proof: $(FILES:.v=.vo)

common: $(COMMON:.v=.vo)
sitpnsimpl: common $(SITPNSIMPL:.v=.vo)
sitpndp: common $(SITPNDP:.v=.vo)
hvhdl: sitpndp $(HVHDL:.v=.vo)
sitpn2hvhdl: sitpndp hvhdl $(SITPN2HVHDL:.v=.vo)
soundness: sitpn2hvhdl $(SOUNDNESS:.v=.vo)

%.vo : %.v	
	@echo "COQC $*.v"
	@$(COQC) $*.v  

cleancommon:
	rm -f $(patsubst %, %/*.vo, common)
	rm -f $(patsubst %, %/.*.aux, common)
	rm -f $(patsubst %, %/*.glob, common)
	rm -f $(patsubst %, %/*.vok, common)
	rm -f $(patsubst %, %/*.vos, common)
	rm -f $(patsubst %, %/*~, common)

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

cleansitpn2hvhdl:
	rm -f $(patsubst %, %/*.vo, sitpn2hvhdl)
	rm -f $(patsubst %, %/.*.aux, sitpn2hvhdl)
	rm -f $(patsubst %, %/*.glob, sitpn2hvhdl)
	rm -f $(patsubst %, %/*.vok, sitpn2hvhdl)
	rm -f $(patsubst %, %/*.vos, sitpn2hvhdl)
	rm -f $(patsubst %, %/*~, sitpn2hvhdl)

cleansoundness:
	rm -f $(patsubst %, %/*.vo, soundness)
	rm -f $(patsubst %, %/.*.aux, soundness)
	rm -f $(patsubst %, %/*.glob, soundness)
	rm -f $(patsubst %, %/*.vok, soundness)
	rm -f $(patsubst %, %/*.vos, soundness)
	rm -f $(patsubst %, %/*~, soundness)

cleanall: cleancommon cleansitpn cleanhvhdl cleansitpn2hvhdl cleansoundness

