# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

# The user can set the CPMODE argument by invoking "make CPMODE=myarg"
# Here, CPMODE stands for Coq Project mode. Use it here to pass the "-p"
# argument to the gen_coqp.sh script.

_CoqProject:
	@echo "Generating _CoqProject file"
	./gen_coqp.sh $(CPMODE)

CoqMakefile: Makefile _CoqProject
	@echo "Generating CoqMakefile file"
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES) 

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
