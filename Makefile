##############################################################################
# Gloval variables

# Host directory used by publish
# Tunneling connection
root_host_dir = asicard@localhost:tmp/FOT

##############################################################################
# Programs

AGDA_FOT     = agda -v 0 -isrc
AGDA_Agsy    = agda -v 0 --allow-unsolved-metas \
                    -isrc -i/home/asr/Agda/std-lib/src/

# N.B. The timeout for the conjectures test should be modify in the
# conjectures_% target.
AGDA2ATP = agda2atp -i. -isrc --unproved-conjecture-error
# AGDA2ATP = agda2atp -i. -isrc --unproved-conjecture-error --only-files
RSYNC    = rsync --archive --progress --rsh='ssh -p 2024'

##############################################################################
# Paths

# Theories
Common_path           = src/Common
DistributiveLaws_path = src/DistributiveLaws
GroupTheory_path      = src/GroupTheory
Logic_path            = src/Logic
LTC_path              = src/LTC
LTC-PCF_path          = src/LTC-PCF
PA_path               = src/PA

# Programs
Division_path = $(LTC-PCF_path)/Program/Division
GCD_path      = $(LTC_path)/Program/GCD
GCD-PCF_path  = $(LTC-PCF_path)/Program/GCD
SortList_path = $(LTC_path)/Program/SortList

##############################################################################
# "main" modules

# Theories
main_Common           = $(Common_path)/Everything

main_DistributiveLaws = $(DistributiveLaws_path)/Everything

main_GroupTheory      = $(GroupTheory_path)/Everything

main_Logic            = $(Logic_path)/Everything

main_LTC              = $(LTC_path)/Everything

main_LTC-PCF          = $(LTC-PCF_path)/Everything

main_PA               = $(PA_path)/Everything

# Agsy examples
# Because we have unsolved-metas in the Agsy examples, we cannot use a
# "main" module.
Agsy_files = $(shell find src/Agsy -name '*.agda' | sort)

# Only used to publish the drafts, i.e. non type checking.
main_Draft = Draft/RenderToHTML

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
		    type_checking_GroupTheory \
		    type_checking_Logic \
		    type_checking_LTC \
		    type_checking_LTC-PCF \
		    type_checking_PA \
		    type_checking_Agsy

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
all_conjectures : conjectures_DistributiveLaws \
		  conjectures_GroupTheory \
		  conjectures_Logic \
		  conjectures_LTC \
		  conjectures_LTC-PCF \
		  conjectures_PA \
                  conjectures_Division \
		  conjectures_GCD \
		  conjectures_GCD-PCF \
		  conjectures_SortList

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
	      publish_GroupTheory \
	      publish_Logic \
	      publish_LTC \
	      publish_LTC-PCF \
	      publish_PA \
              publish_Agsy

##############################################################################
# Other stuff

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
