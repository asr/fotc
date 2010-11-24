##############################################################################
# Gloval variables

# Host directory used by publish
# Tunneling connection
root_host_dir = asicard@localhost:tmp/LTC

##############################################################################
# Programs

AGDA     = agda -v 0 -i. -isrc
AGDA2ATP = agda2atp -i. -isrc --unproved-conjecture-error
RSYNC    = rsync --archive --progress --rsh='ssh -p 2024'

##############################################################################
# Paths

Common_path      = src/Common
LTC_path         = src/LTC
LTC-PCF_path     = src/PCF/LTC
Division_path    = src/PCF/Examples/Division
GCD_path         = src/Examples/GCD
GCD-PCF_path     = src/PCF/Examples/GCD
Logic_path       = src/Examples/Logic/NonATP
LogicATP_path    = src/Examples/Logic/ATP
SortList_path    = src/Examples/SortList
Consistency_path = Test/Consistency

##############################################################################
# "main" modules

main_module_Common      = $(Common_path)/Everything

main_module_LTC         = $(LTC_path)/Everything
main_module_ER_LTC      = $(LTC_path)/EverythingER

main_module_LTC-PCF     = $(LTC-PCF_path)/Everything
main_module_ER_LTC-PCF  = $(LTC-PCF_path)/EverythingER

main_module_Division    = $(Division_path)/ProofSpecification
main_module_ER_Division = $(Division_path)/ProofSpecificationER

main_module_GCD         = $(GCD_path)/ProofSpecification
main_module_ER_GCD      = $(GCD_path)/ProofSpecificationER

main_module_GCD-PCF     = $(GCD-PCF_path)/ProofSpecification
main_module_ER_GCD-PCF  = $(GCD-PCF_path)/ProofSpecificationER

main_module_Logic       = $(Logic_path)/Logic

main_module_LogicATP    = $(LogicATP_path)/Logic

main_module_SortList    = $(SortList_path)/ProofSpecification
main_module_ER_SortList = $(SortList_path)/ProofSpecificationER

main_module_Consistency = $(Consistency_path)/Readme

# Only used to publish the drafts, i.e. non type checking.
main_module_Draft       = Draft/RenderToHTML

##############################################################################
# Type checking the Agda modules.

type_checking_ER_% :
	$(AGDA) ${main_module_ER_$*}.agda

type_checking_% :
	$(AGDA) ${main_module_$*}.agda


all_type_checking_NER : type_checking_Common \
			type_checking_LTC \
			type_checking_LTC-PCF \
			type_checking_Division \
			type_checking_GCD \
			type_checking_GCD-PCF \
			type_checking_Logic \
			type_checking_LogicATP \
			type_checking_SortList \
			type_checking_Consistency \

all_type_checking_ER  : type_checking_ER_LTC \
			type_checking_ER_LTC-PCF \
			type_checking_ER_Division \
			type_checking_ER_GCD \
			type_checking_ER_GCD-PCF \
			type_checking_ER_SortList

all_type_checking     : all_type_checking_NER all_type_checking_ER

##############################################################################
# Test the conjecture files.

# The time limit should be the maximum (720 sec) which is required
# by Examples.SortList.Closures.TreeOrd.rightSubTree-TreeOrd.
conjectures_% :
	for file in \
          `find $($*_path) -name '*.agda' | xargs grep -l 'ATP prove'`; do \
            if ! ( ${AGDA} $${file} ); then exit 1; fi; \
	    if ! ( ${AGDA2ATP} --time=300 $${file} ); then exit 1; fi; \
	done

all_conjectures : conjectures_LTC \
		  conjectures_LTC-PCF \
                  conjectures_Division \
		  conjectures_GCD \
		  conjectures_GCD-PCF \
		  conjectures_LogicATP \
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

all_publish : publish_Common \
	      publish_LTC \
	      publish_LTC-PCF \
	      publish_Division \
	      publish_GCD \
	      publish_GCD-PCF \
	      publish_Logic \
	      publish_LogicATP \
	      publish_SortList \
	      publish_Consistency

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
