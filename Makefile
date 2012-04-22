##############################################################################
# Global variables

publish = $(shell if [ -e publish.mk ]; then echo Yes; else echo No; fi)
ifeq ($(publish),Yes)
include publish.mk
endif

# Snapshot directory
snapshot_dir = snapshot

##############################################################################
# Programs

# The current directory (\ie. '.') in the Agda path is required only
# for work with the Draft directory.
AGDA_FOT  = agda -v 0 -i. -isrc
AGDA_Agsy = agda -v 0 --allow-unsolved-metas \
                 -isrc -i/home/asr/Agda/std-lib/src/

# N.B. The timeout for the conjectures test should be modify in the
# conjectures_% target.
AGDA2ATP = agda2atp -i. -isrc
# AGDA2ATP = agda2atp -i. -isrc --atp=e
# AGDA2ATP = agda2atp -i. -isrc --atp=equinox
# AGDA2ATP = agda2atp -i. -isrc --atp=metis
# AGDA2ATP = agda2atp -i. -isrc --atp=spass
# AGDA2ATP = agda2atp -i. -isrc --atp=vampire
AGDA2ATP_CREATE_SNAPSHOT = agda2atp -i. -isrc --only-files \
                                    --output-dir=$(snapshot_dir)
AGDA2ATP_SNAPSHOT_TEST = agda2atp -i. -isrc --snapshot-test \
                                  --snapshot-dir=$(snapshot_dir)
AGDA2ATP_ONLY_CONJECTURES = agda2atp -i. -isrc --only-files

# Equinox has the better parser for TPTP files, so we use it to find problems.
# See notes/tptp/parsing_error.tptp
AGDA2ATP_PARSING = agda2atp -i. -isrc --time=1 --atp=equinox

##############################################################################
# Paths

# Theories
Common_path           = src/Common
DistributiveLaws_path = src/DistributiveLaws
FOL_path              = src/FOL
FOTC_path             = src/FOTC
GroupTheory_path      = src/GroupTheory
LTC-PCF_path          = src/LTC-PCF
PA_path               = src/PA

# Programs
ABP_path             = $(FOTC_path)/Program/ABP
Collatz_path         = $(FOTC_path)/Program/Collatz
Division_path        = $(FOTC_path)/Program/Division
Division-PCF_path    = $(LTC-PCF_path)/Program/Division
GCD-Partial_path     = $(FOTC_path)/Program/GCD/Partial
GCD-Total_path       = $(FOTC_path)/Program/GCD/Total
GCD-PCF-Partial_path = $(LTC-PCF_path)/Program/GCD/Partial
MapIterate_path      = $(FOTC_path)/Program/MapIterate
McCarthy91_path      = $(FOTC_path)/Program/McCarthy91
Mirror_path          = $(FOTC_path)/Program/Mirror
SortList_path        = $(FOTC_path)/Program/SortList

##############################################################################
# Everything modules

# Theories
everything_Common           = $(Common_path)/Everything
everything_DistributiveLaws = $(DistributiveLaws_path)/Everything
everything_FOL              = $(FOL_path)/Everything
everything_FOTC             = $(FOTC_path)/Everything
everything_GroupTheory      = $(GroupTheory_path)/Everything
everything_LTC-PCF          = $(LTC-PCF_path)/Everything
everything_PA               = $(PA_path)/Everything

# Agsy examples
#
# Because we have unsolved-metas in the Agsy examples, we cannot use a
# Everything module.
Agsy_files = $(shell find src/Agsy -name '*.agda' | sort)

# Only used to publish the drafts, i.e. non type checking.
everything_Draft = Draft/RenderToHTML

# The README everything
everything_README = README

##############################################################################
# Conjectures

define conjectures
$(shell find $($(*)_path) -name '*.agda' | \
        xargs grep -l 'ATP prove' | \
        xargs grep -L 'ConsistencyTest' | \
        sort)
endef

##############################################################################
# Type checking the Agda modules

type_checking_Agsy : $(Agsy_files)
	for file in $(Agsy_files); do \
	  $(AGDA_Agsy) $${file}; \
	done

type_checking_% :
	$(AGDA_FOT) $(everything_$*).agda

all_type_checking : type_checking_Common \
		    type_checking_DistributiveLaws \
		    type_checking_FOL \
		    type_checking_FOTC \
		    type_checking_GroupTheory \
		    type_checking_LTC-PCF \
		    type_checking_PA \
		    type_checking_Agsy \
		    type_checking_README
	@echo "The $@ test succeeded!"

##############################################################################
# Only create the conjecture files

only_conjectures_% :
	for file in $(conjectures); do \
	    echo "Processing file $$file"; \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if ! ( $(AGDA2ATP_ONLY_CONJECTURES) $${file} ); then exit 1; fi; \
	done

all_only_conjectures : only_conjectures_DistributiveLaws \
		       only_conjectures_FOL \
		       only_conjectures_FOTC \
		       only_conjectures_GroupTheory \
		       only_conjectures_LTC-PCF \
		       only_conjectures_PA
	@echo "The $@ test succeeded!"

##############################################################################
# Only parsing the conjecture files

parsing_% :
	for file in $(conjectures); do \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if ! ( $(AGDA2ATP_PARSING) $${file} \
                                       >/tmp/xxx.tmp \
                                       2>/tmp/parsing.error ); then \
		exit 1; \
	    fi; \
	    if [ -s /tmp/parsing.error ]; then \
		echo "Parsing error in $${file}"; \
		exit 1; \
	    fi; \
	done

all_parsing : parsing_DistributiveLaws \
	      parsing_FOL \
	      parsing_FOTC \
	      parsing_GroupTheory \
	      parsing_LTC-PCF \
	      parsing_PA
	@echo "The $@ test succeeded!"

##############################################################################
# Test the conjecture files

conjectures_% :
	for file in $(conjectures); do \
	    echo "Processing file $$file"; \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if ! ( $(AGDA2ATP) --time=180 $${file} ); then exit 1; fi; \
	done

# TODO: We add the conjectures related to the programs, but it
# duplicates the test.
# all_conjectures : conjectures_DistributiveLaws \
# 		  conjectures_FOL \
# 		  conjectures_FOTC \
# 		  conjectures_GroupTheory \
# 		  conjectures_LTC-PCF \
# 		  conjectures_PA \
#                 conjectures_ABP \
#                 conjectures_Collatz \
#                 conjectures_Division \
#                 conjectures_Division-PCF \
# 		  conjectures_GCD-Partial \
# 		  conjectures_GCD-Total \
# 		  conjectures_GCD-PCF-Partial \
#		  conjectures_MapIterate \
#		  conjectures_McCarthy91 \
#		  conjectures_Mirror \
# 		  conjectures_SortList

all_conjectures : conjectures_DistributiveLaws \
		  conjectures_FOL \
		  conjectures_FOTC \
		  conjectures_GroupTheory \
		  conjectures_LTC-PCF \
		  conjectures_PA
	@echo "The $@ test succeeded!"

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
	@echo "The $@ test succeeded!"

##############################################################################
# Create snapshot files

create_snapshot_% :
	for file in $(conjectures); do \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if ! ( $(AGDA2ATP_CREATE_SNAPSHOT) $${file} ); then exit 1; fi; \
	done

all_create_snapshot : create_snapshot_DistributiveLaws \
		      create_snapshot_FOL \
		      create_snapshot_FOTC \
		      create_snapshot_GroupTheory \
		      create_snapshot_LTC-PCF \
		      create_snapshot_PA

##############################################################################
# Test the snapshot files

snapshot_% :
	for file in $(conjectures); do \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if ! ( $(AGDA2ATP_SNAPSHOT_TEST) $${file} ); then exit 1; fi; \
	done

all_snapshot : snapshot_DistributiveLaws \
	       snapshot_FOL \
	       snapshot_FOTC \
	       snapshot_GroupTheory \
	       snapshot_LTC-PCF \
	       snapshot_PA
	@echo "The $@ test succeeded!"

##############################################################################
# Test used when there is a modification to Agda

agda_changed : clean_interfaces all_type_checking all_only_conjectures
	@echo "The $@ test succeeded!"

##############################################################################
# Publish the .html files

publish_note :
	$(RSYNC) html/ $(root_host_dir)/notes/
	rm -r html

publish_Agsy : $(Agsy_files)
	rm -r -f /tmp/Agsy/html/
	for file in $(Agsy_files); do \
	  $(AGDA_Agsy) --html --html-dir=/tmp/Agsy/html/ $${file}; \
	done
	$(RSYNC) /tmp/Agsy/html/ $(root_host_dir)/Agsy/

publish_% :
	rm -r -f /tmp/$*/html/
	$(AGDA_FOT) --html --html-dir=/tmp/$*/html/ $(everything_$*).agda
	$(RSYNC) /tmp/$*/html/ $(root_host_dir)/$*/

all_publish : publish_Common \
	      publish_DistributiveLaws \
	      publish_FOL \
	      publish_FOTC \
	      publish_GroupTheory \
	      publish_LTC-PCF \
	      publish_PA \
              publish_Agsy

##############################################################################
# Other stuff

dependency_graph : src/FOTC/Program/GCD/Total/ProofSpecificationATP.agda
	$(AGDA_FOT) --dependency-graph=/tmp/dependency-graph-gcd.gv $<
	dot -Tps /tmp/dependency-graph-gcd.gv > /tmp/dependency-graph-gcd.ps

TODO :
	find src/ -name '*.agda' | xargs grep TODO

clean_interfaces :
	find -name '*.agdai' | xargs rm -f

clean : clean_interfaces
	rm -f /tmp/*.tptp

##############################################################################
# Main

all_tests : all_type_checking all_conjectures all_consistency
	@echo "The $@ test succeeded!"
