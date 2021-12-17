# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile

# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

gen-coqproject-p-option:
	@echo "Generating _CoqProject file, including proof files"
	./gen_coqp.sh -p

gen-coqproject-no-option:
	@echo "Generating _CoqProject file, without proof files"
	./gen_coqp.sh

CoqMakefile:
	@if [ ! -e _CoqProject ]; then\
		@echo "No _CoqProject file found";\
		@echo "Generating _CoqProject file, without proof files";\
		./gen_coqp.sh;\
	fi
	@echo "Generating CoqMakefile file"
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

with-proof: gen-coqproject-p-option
	@make

without-proof: gen-coqproject-no-option
	@make

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
