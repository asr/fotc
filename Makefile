##############################################################################
# Gloval variables

# Host directory used by publish
# Tunneling connection
root_host_dir = asicard@localhost:tmp/FOT

##############################################################################
# Programs

AGDA     = agda -v 0 -i. -isrc
AGDA2ATP = agda2atp -i. -isrc --unproved-conjecture-error
RSYNC    = rsync --archive --progress --rsh='ssh -p 2024'

##############################################################################
# Paths

# Theories
AbelianGroupTheory_path = src/AbelianGroupTheory
AxiomaticPA_path        = src/AxiomaticPA
Common_path             = src/Common
GroupTheory_path        = src/GroupTheory
Logic_path              = src/Logic/NonATP
LogicATP_path           = src/Logic/ATP
LTC_path                = src/LTC
LTC-PCF_path            = src/LTC-PCF
PA_path                 = src/PA

# Programs
Division_path    = $(LTC-PCF_path)/Program/Division
GCD_path         = $(LTC_path)/Program/GCD
GCD-PCF_path     = $(LTC-PCF_path)/Program/GCD
SortList_path    = $(LTC_path)/Program/SortList

##############################################################################
# "main" modules

# Theories
main_AbelianGroupTheory = $(AbelianGroupTheory_path)/Everything

main_AxiomaticPA        = $(AxiomaticPA_path)/Everything

main_Common             = $(Common_path)/Everything

main_GroupTheory        = $(GroupTheory_path)/Everything
main_GroupTheory_ER     = $(GroupTheory_path)/EverythingER

main_Logic              = $(Logic_path)/Logic

main_LogicATP           = $(LogicATP_path)/Logic

main_LTC                = $(LTC_path)/Everything
main_LTC_ER             = $(LTC_path)/EverythingER

main_LTC-PCF            = $(LTC-PCF_path)/Everything
main_LTC-PCF_ER         = $(LTC-PCF_path)/EverythingER

main_PA                 = $(PA_path)/Properties

# Only used to publish the drafts, i.e. non type checking.
main_Draft              = Draft/RenderToHTML

##############################################################################
# Type checking the Agda modules.

type_checking_ER_% :
	$(AGDA) ${main_$*_ER}.agda

type_checking_% :
	$(AGDA) ${main_$*}.agda

all_type_checking_NER : type_checking_AbelianGroupTheory \
			type_checking_AxiomaticPA \
			type_checking_Common \
			type_checking_GroupTheory \
			type_checking_Logic \
			type_checking_LogicATP \
			type_checking_LTC \
			type_checking_LTC-PCF \
			type_checking_PA

all_type_checking_ER  : type_checking_GroupTheory_ER \
			type_checking_LTC_ER \
			type_checking_LTC-PCF_ER

all_type_checking     : all_type_checking_NER all_type_checking_ER

##############################################################################
# Test the conjecture files.

conjectures_% :
	for file in \
          `find $($*_path) -name '*.agda' | xargs grep -l 'ATP prove' | xargs grep -L 'ConsistencyTest'`; do \
            if ! ( ${AGDA} $${file} ); then exit 1; fi; \
	    if ! ( ${AGDA2ATP} --time=300 $${file} ); then exit 1; fi; \
	done

# TODO: We add the conjectures related to the programs, but it
# duplicates the test.
all_conjectures : conjectures_AbelianGroupTheory \
	          conjectures_AxiomaticPA \
		  conjectures_GroupTheory \
		  conjectures_LogicATP \
		  conjectures_LTC \
		  conjectures_LTC-PCF \
		  conjectures_PA \
                  conjectures_Division \
		  conjectures_GCD \
		  conjectures_GCD-PCF \
		  conjectures_SortList

##############################################################################
# Consistency test

# Consistency test files
# AbelianGroupTheory.Base.ConsistencyTest
# AxiomaticPA.Base.ConsistencyTest
# GroupTheory.Base.ConsistencyTest
# GroupTheory.Groupoids.Base.ConsistencyTest
# LTC.Base.ConsistencyTest.agda
# LTC.Data.Bool.ConsistencyTest.agda
# LTC.Data.List.ConsistencyTest.agda
# LTC.Data.Nat.ConsistencyTest.agda
# LTC.Data.Nat.Inequalities.ConsistencyTest.agda
# LTC.Data.Stream.Bisimilarity.ConsistencyTest
# LTC.Program.GCD.GCD.ConsistencyTest
# LTC.Program.SortList.SortList.ConsistencyTest

# Because we are using the option --unproved-conjecture-error we
# revert the agda2atp output.
# all_consistency :
# 	for file in \
#           `find $(Consistency_path) -name '*.agda' | xargs grep -l 'ATP prove'`; do \
#             if ! ( ${AGDA} $${file} ); then exit 1; fi; \
# 	    if ( ${AGDA2ATP} --time=10 $${file} ); then exit 1; fi; \
# 	done

##############################################################################
# Publish the .html files

# html_dir_XXX = /tmp/XXX/html/
# host_dir_XXX = $(root_host_dir)/XXX/

publish_% :
	rm -r -f /tmp/$*/html/
	$(AGDA) --html --html-dir=/tmp/$*/html/ ${main_$*}.agda
	$(RSYNC) /tmp/$*/html/ $(root_host_dir)/$*/

all_publish : publish_AbelianGroupTheory \
	      publish_AxiomaticPA \
	      publish_Common \
	      publish_GroupTheory \
	      publish_Logic \
	      publish_LogicATP \
	      publish_LTC \
	      publish_LTC-PCF \
	      publish_PA

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
