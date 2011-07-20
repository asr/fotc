##############################################################################
# Gloval variables

# Host directory used by publish
# Tunneling connection
root_host_dir = asicard@localhost:code/fotc/FOT

##############################################################################
# Programs

# The current directory (\ie. '.') in the Agda path is required only
# for work with the Draft directory.
AGDA_FOT     = agda -v 0 -i. -isrc
AGDA_Agsy    = agda -v 0 --allow-unsolved-metas \
                    -isrc -i/home/asr/Agda/std-lib/src/

# N.B. The timeout for the conjectures test should be modify in the
# conjectures_% target.
AGDA2ATP                  = agda2atp -i. -isrc --unproved-conjecture-error
AGDA2ATP_ONLY_CONJECTURES = agda2atp -i. -isrc --only-files
RSYNC                     = rsync --archive --progress --rsh='ssh -p 2024'

##############################################################################
# Paths

# Theories
Common_path           = src/Common
DistributiveLaws_path = src/DistributiveLaws
FOTC_path             = src/FOTC
GroupTheory_path      = src/GroupTheory
LTC-PCF_path          = src/LTC-PCF
PA_path               = src/PA
PredicateLogic_path   = src/PredicateLogic

# Programs
Collatz_path        = $(FOTC_path)/Program/Collatz
Division_path       = $(FOTC_path)/Program/Division
Division-PCF_path   = $(LTC-PCF_path)/Program/Division
GCDPartial_path     = $(FOTC_path)/Program/GCD/Partial
GCDTotal_path       = $(FOTC_path)/Program/GCD/Total
GCD-PCFPartial_path = $(LTC-PCF_path)/Program/GCD/Partial
MapIterate_path     = $(FOTC_path)/Program/MapIterate
McCarthy91_path     = $(FOTC_path)/Program/McCarthy91
Mirror_path         = $(FOTC_path)/Program/Mirror
SortList_path       = $(FOTC_path)/Program/SortList

##############################################################################
# "main" modules

# Theories
main_Common           = $(Common_path)/Everything

main_DistributiveLaws = $(DistributiveLaws_path)/Everything

main_FOTC             = $(FOTC_path)/Everything

main_GroupTheory      = $(GroupTheory_path)/Everything

main_LTC-PCF          = $(LTC-PCF_path)/Everything

main_PA               = $(PA_path)/Everything

main_PredicateLogic   = $(PredicateLogic_path)/Everything

# Agsy examples
# Because we have unsolved-metas in the Agsy examples, we cannot use a
# "main" module.
Agsy_files = $(shell find src/Agsy -name '*.agda' | sort)

# Only used to publish the drafts, i.e. non type checking.
main_Draft = Draft/RenderToHTML

# The README main
main_README = README

##############################################################################
# Type checking the Agda modules.

type_checking_Agsy : $(Agsy_files)
	for file in $(Agsy_files); do \
	  $(AGDA_Agsy) $${file}; \
	done

type_checking_% :
	$(AGDA_FOT) $(main_$*).agda

all_type_checking : type_checking_Common \
		    type_checking_DistributiveLaws \
		    type_checking_FOTC \
		    type_checking_GroupTheory \
		    type_checking_LTC-PCF \
		    type_checking_PA \
		    type_checking_PredicateLogic \
		    type_checking_Agsy \
		    type_checking_README

##############################################################################
# Only create the conjecture files.

only_conjectures_% :
	for file in \
          `find $($*_path) -name '*.agda' | xargs grep -l 'ATP prove' | xargs grep -L 'ConsistencyTest' | sort`; do \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if ! ( $(AGDA2ATP_ONLY_CONJECTURES) $${file} ); then exit 1; fi; \
	done

all_only_conjectures : only_conjectures_DistributiveLaws \
		       only_conjectures_FOTC \
		       only_conjectures_GroupTheory \
		       only_conjectures_LTC-PCF \
		       only_conjectures_PA \
		       only_conjectures_PredicateLogic \

##############################################################################
# Test the conjecture files.

conjectures_% :
	for file in \
          `find $($*_path) -name '*.agda' | xargs grep -l 'ATP prove' | xargs grep -L 'ConsistencyTest' | sort`; do \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if ! ( $(AGDA2ATP) --time=180 $${file} ); then exit 1; fi; \
	done

# TODO: We add the conjectures related to the programs, but it
# duplicates the test.
# all_conjectures : conjectures_DistributiveLaws \
# 		  conjectures_FOTC \
# 		  conjectures_GroupTheory \
# 		  conjectures_LTC-PCF \
# 		  conjectures_PA \
# 		  conjectures_PredicateLogic \
#                 conjectures_Collatz \
#                 conjectures_Division \
#                 conjectures_Division-PCF \
# 		  conjectures_GCDPartial \
# 		  conjectures_GCDTotal \
# 		  conjectures_GCD-PCFPartial \
#		  conjectures_MapIterate \
#		  conjectures_McCarthy91 \
#		  conjectures_Mirror \
# 		  conjectures_SortList

all_conjectures : conjectures_DistributiveLaws \
		  conjectures_FOTC \
		  conjectures_GroupTheory \
		  conjectures_LTC-PCF \
		  conjectures_PA \
		  conjectures_PredicateLogic \

##############################################################################
# Consistency test

consistency_test_files = $(patsubst %.agda,%, \
	$(shell find src/ -name '*ConsistencyTest.agda' | sort))

# Because we are using the option --unproved-conjecture-error we
# revert the agda2atp output.
$(consistency_test_files) :
	if ! ( $(AGDA_FOT) $@.agda ); then exit 1; fi; \
	if ( $(AGDA2ATP) --time=10 $@.agda ); then exit 1; fi; \

all_consistency : $(consistency_test_files)

##############################################################################
# Publish the .html files

# html_dir_XXX = /tmp/XXX/html/
# host_dir_XXX = $(root_host_dir)/XXX/

publish_Agsy : $(Agsy_files)
	rm -r -f /tmp/Agsy/html/
	for file in $(Agsy_files); do \
	  $(AGDA_Agsy) --html --html-dir=/tmp/Agsy/html/ $${file}; \
	done
	$(RSYNC) /tmp/Agsy/html/ $(root_host_dir)/Agsy/

publish_% :
	rm -r -f /tmp/$*/html/
	$(AGDA_FOT) --html --html-dir=/tmp/$*/html/ $(main_$*).agda
	$(RSYNC) /tmp/$*/html/ $(root_host_dir)/$*/

all_publish : publish_Common \
	      publish_DistributiveLaws \
	      publish_FOTC \
	      publish_GroupTheory \
	      publish_LTC-PCF \
	      publish_PA \
	      publish_PredicateLogic \
              publish_Agsy

##############################################################################
# Other stuff

dependency_graph : src/FOTC/Program/GCD/Total/ProofSpecificationATP.agda
	$(AGDA_FOT) --dependency-graph=/tmp/dependency-graph-gcd.gv $<
	dot -Tps /tmp/dependency-graph-gcd.gv > /tmp/dependency-graph-gcd.ps

TODO :
	@find src/ -name '*.agda' | xargs grep TODO

clean :
	@find -name '*.agdai' | xargs rm -f
	@rm -f /tmp/*.tptp

##############################################################################
# Main

all_test : all_type_checking all_conjectures all_consistency

# TODO
# non_conjectures :
# 	./Test/non-conjectures.bash
