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
AxiomaticPA_path = src/AxiomaticPA
Common_path      = src/Common
GroupTheory_path = src/GroupTheory
Logic_path       = src/Logic/NonATP
LogicATP_path    = src/Logic/ATP
LTC_path         = src/LTC
LTC-PCF_path     = src/LTC-PCF
PA_path          = src/PA

# Programs
Division_path    = $(LTC-PCF_path)/Program/Division
GCD_path         = $(LTC_path)/Program/GCD
GCD-PCF_path     = $(LTC-PCF_path)/Program/GCD
SortList_path    = $(LTC_path)/Program/SortList

# Others
Consistency_path = Test/Consistency

##############################################################################
# "main" modules

# Theories
main_module_AxiomaticPA = $(AxiomaticPA_path)/Properties

main_module_Common      = $(Common_path)/Everything

main_module_GroupTheory = $(GroupTheory_path)/Properties

main_module_Logic       = $(Logic_path)/Logic

main_module_LogicATP    = $(LogicATP_path)/Logic

main_module_LTC         = $(LTC_path)/Everything
main_module_ER_LTC      = $(LTC_path)/EverythingER

main_module_LTC-PCF     = $(LTC-PCF_path)/Everything
main_module_ER_LTC-PCF  = $(LTC-PCF_path)/EverythingER

main_module_PA          = $(PA_path)/Properties

# Others
main_module_Consistency = $(Consistency_path)/README

# Only used to publish the drafts, i.e. non type checking.
main_module_Draft       = Draft/RenderToHTML

##############################################################################
# Type checking the Agda modules.

type_checking_ER_% :
	$(AGDA) ${main_module_ER_$*}.agda

type_checking_% :
	$(AGDA) ${main_module_$*}.agda


all_type_checking_NER : type_checking_AxiomaticPA \
			type_checking_Common \
			type_checking_GroupTheory \
			type_checking_Logic \
			type_checking_LogicATP \
			type_checking_LTC \
			type_checking_LTC-PCF \
			type_checking_PA \
			type_checking_Consistency

all_type_checking_ER  : type_checking_ER_LTC \
			type_checking_ER_LTC-PCF

all_type_checking     : all_type_checking_NER all_type_checking_ER

##############################################################################
# Test the conjecture files.

conjectures_% :
	for file in \
          `find $($*_path) -name '*.agda' | xargs grep -l 'ATP prove'`; do \
            if ! ( ${AGDA} $${file} ); then exit 1; fi; \
	    if ! ( ${AGDA2ATP} --time=300 $${file} ); then exit 1; fi; \
	done

# TODO: We add the conjectures related to the programs, but it
# duplicates the test.
all_conjectures : conjectures_AxiomaticPA \
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

# Because we are using the option --unproved-conjecture-error we
# revert the agda2atp output.
all_consistency :
	for file in \
          `find $(Consistency_path) -name '*.agda' | xargs grep -l 'ATP prove'`; do \
            if ! ( ${AGDA} $${file} ); then exit 1; fi; \
	    if ( ${AGDA2ATP} --time=10 $${file} ); then exit 1; fi; \
	done

##############################################################################
# Publish the .html files

# html_dir_XXX = /tmp/XXX/html/
# host_dir_XXX = $(root_host_dir)/XXX/

publish_% :
	rm -r -f /tmp/$*/html/
	$(AGDA) --html --html-dir=/tmp/$*/html/ ${main_module_$*}.agda
	$(RSYNC) /tmp/$*/html/ $(root_host_dir)/$*/

all_publish : publish_AxiomaticPA \
	      publish_Common \
	      publish_GroupTheory \
	      publish_Logic \
	      publish_LogicATP \
	      publish_LTC \
	      publish_LTC-PCF \
	      publish_PA \
	      publish_Consistency

##############################################################################
# Other stuff

TODO :
	@find src/ Test/ -name '*.agda' | xargs grep TODO

clean :
	@find -name '*.agdai' | xargs rm -f
	@rm -f /tmp/*.tptp

##############################################################################
# Main

all_test : all_type_checking all_conjectures all_consistency

# TODO
# non_conjectures :
# 	./Test/non-conjectures.bash
