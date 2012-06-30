##############################################################################
# Global variables

publish = $(shell if [ -e publish.mk ]; then echo Yes; else echo No; fi)
ifeq ($(publish),Yes)
include publish.mk
endif

# Snapshot directory.
snapshot_dir = snapshot

# Directory for the TPTP files.
output_dir = /tmp/FOT

# Agda standard library path.
std_lib_path = /home/asr/agda-upstream/std-lib

##############################################################################
# Programs

# The current directory (\ie. '.') in the Agda path is required only
# for work with the Draft directory.
AGDA_FOT   = agda -v 0 -i. -isrc
AGDA_Agsy  = agda -v 0 -isrc -i$(std_lib_path)/src/
AGDA_notes = agda -v 0 \
	      	  -inotes \
		  -inotes/fixed-points \
		  -inotes/papers/FoSSaCS-2012 \
		  -inotes/papers/paper-2011/ \
		  -inotes/setoids/ \
		  -inotes/thesis/logical-framework/ \
	          -i$(std_lib_path)/src/ \
                  -isrc \

# N.B. The timeout for the conjectures test should be modify in the
# conjectures_% target.
AGDA2ATP = agda2atp -i. -isrc --output-dir=$(output_dir)
# AGDA2ATP = agda2atp -i. -isrc --atp=e --output-dir=$(output_dir)
# AGDA2ATP = agda2atp -i. -isrc --atp=equinox --output-dir=$(output_dir)
# AGDA2ATP = agda2atp -i. -isrc --atp=metis --output-dir=$(output_dir)
# AGDA2ATP = agda2atp -i. -isrc --atp=spass --output-dir=$(output_dir)
# AGDA2ATP = agda2atp -i. -isrc --atp=vampire --output-dir=$(output_dir)
AGDA2ATP_SNAPSHOT_CREATE = agda2atp -i. -isrc --only-files \
                                    --output-dir=$(snapshot_dir)
AGDA2ATP_SNAPSHOT_TEST = agda2atp -i. -isrc --snapshot-test \
                                  --snapshot-dir=$(snapshot_dir)

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

# Agsy and notes examples
#
# Because we have unsolved-metas in the Agsy and notes examples, we
# cannot use an Everything module.
Agsy_files = $(shell find src/Agsy -name '*.agda' | sort)

# Notes files
notes_files = $(shell find notes/ -name '*.agda' | sort)

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
	cd $(std_lib_path) && darcs pull
	for file in $(Agsy_files); do \
	    if ! ( $(AGDA_Agsy) $${file} ); then exit 1; fi; \
	done

type_checking_notes : $(notes_files)
	cd $(std_lib_path) && darcs pull
	for file in $(notes_files); do \
	    if ! ( $(AGDA_notes) $${file} ); then exit 1; fi; \
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
		    type_checking_README \
		    type_checking_Agsy \
	            type_checking_notes
	@echo "The $@ test succeeded!"

##############################################################################
# Only create the conjecture files

only_conjectures_% :
	for file in $(conjectures); do \
	    echo "Processing $${file}"; \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if [ "src/FOL/NonIntuitionistic/TheoremsATP.agda" = $${file} ] || \
               [ "src/FOL/SchemataATP.agda" = $${file} ]; then \
	       if ! ( $(AGDA2ATP) --only-files --non-fol $${file} ); then exit 1; fi; \
            else \
	      if ! ( $(AGDA2ATP) --only-files $${file} ); then exit 1; fi; \
            fi; \
	    # Comparison of the generated conjectures against the \
	    # current ones. However we prefer to use the snapshot \
	    # test to avoid keep the conjectures in the repository. \
	    # tmp1=$${file%.agda}; \
	    # tmp2=$${tmp1#src/}; \
	    # if ! ( diff -r $(output_dir)/$${tmp2} src/$${tmp2} ); then exit 1; fi; \
	done

all_only_conjectures : only_conjectures_DistributiveLaws \
		       only_conjectures_FOL \
		       only_conjectures_FOTC \
		       only_conjectures_GroupTheory \
		       only_conjectures_PA
	@echo "The $@ test succeeded!"

##############################################################################
# Only parsing the conjecture files

# We use tptp4X from the TPTP v5.4.0 to parse the TPTP files. See
# notes/tptp/parsing_error.tptp
parsing_% :
	for file in $(conjectures); do \
	    echo "Processing $${file}"; \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if ! ( $(AGDA2ATP) --non-fol --only-files $${file} ); then exit 1; fi; \
	    find $(output_dir) | while read tptp_file; do \
              if ! ( tptp4X $${tptp_file} ); then exit 1; fi; \
	    done; \
	done

all_parsing : parsing_DistributiveLaws \
	      parsing_FOL \
	      parsing_FOTC \
	      parsing_GroupTheory \
	      parsing_PA
	@echo "The $@ test succeeded!"

##############################################################################
# Test the conjecture files

conjectures_% :
	for file in $(conjectures); do \
	    echo "Processing $${file}"; \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if [ "src/FOL/NonIntuitionistic/TheoremsATP.agda" = $${file} ] || \
               [ "src/FOL/SchemataATP.agda" = $${file} ]; then \
	       if ! ( $(AGDA2ATP) --non-fol --time=240 $${file} ); then exit 1; fi; \
            else \
	      if ! ( $(AGDA2ATP) --time=240 $${file} ); then exit 1; fi; \
            fi; \
	done

# TODO: We add the conjectures related to the programs, but it
# duplicates the test.
# all_conjectures : conjectures_DistributiveLaws \
# 		  conjectures_FOL \
# 		  conjectures_FOTC \
# 		  conjectures_GroupTheory \
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

snapshot_create_% :
	for file in $(conjectures); do \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if ! ( $(AGDA2ATP_SNAPSHOT_CREATE) --non-fol $${file} ); then \
	       exit 1; \
            fi; \
	done

all_snapshot_create : snapshot_clean \
		      snapshot_create_DistributiveLaws \
		      snapshot_create_FOL \
		      snapshot_create_FOTC \
		      snapshot_create_GroupTheory \
		      snapshot_create_PA
	@echo "$@ succeeded!"

snapshot_clean :
	rm -r -f $(snapshot_dir)

##############################################################################
# Test the snapshot files

snapshot_test_% :
	for file in $(conjectures); do \
	    echo "Processing $${file}"; \
            if ! ( $(AGDA_FOT) $${file} ); then exit 1; fi; \
	    if ! ( $(AGDA2ATP_SNAPSHOT_TEST) --non-fol $${file} ); then \
	       exit 1; \
        fi; \
	done

all_snapshot_test : snapshot_test_DistributiveLaws \
	            snapshot_test_FOL \
	            snapshot_test_FOTC \
	            snapshot_test_GroupTheory \
	            snapshot_test_PA
	@echo "The $@ test succeeded!"

##############################################################################
# Test used when there is a modification to Agda

agda_changed : agda_changed_clean all_type_checking all_only_conjectures
	@echo "The $@ test succeeded!"

agda_changed_clean :
	find -name '*.agdai' | xargs rm -f

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
	find -name '*.*' | xargs grep -I TODO | sort

clean :
	find -name '*.agdai' | xargs rm -f
	rm -f -r $(output_dir)

##############################################################################
# Main

all_tests : all_type_checking all_conjectures all_consistency
	@echo "The $@ test succeeded!"
