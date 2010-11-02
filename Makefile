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
# "main" files

main_file_NER_LTC         = src/LTC/Everything
main_file_ER_LTC          = src/LTC/EverythingER

main_file_NER_LTC-PCF     = src/LTC-PCF/Everything
main_file_ER_LTC-PCF      = src/LTC-PCF/EverythingER

main_file_NER_DivisionPCF = src/Examples/DivisionPCF/ProofSpecificationPCF
main_file_ER_DivisionPCF  = src/Examples/DivisionPCF/ProofSpecificationPCF-ER

main_file_NER_GCD         = src/Examples/GCD/ProofSpecification
main_file_ER_GCD          = src/Examples/GCD/ProofSpecificationER

main_file_NER_GCD-PCF     = src/Examples/GCD-PCF/ProofSpecificationPCF
main_file_ER_GCD-PCF      = src/Examples/GCD-PCF/ProofSpecificationPCF-ER

main_file_NER_Logic       = src/Examples/Logic/Logic

main_file_NER_SortList    = src/Examples/SortList/ProofSpecification
main_file_ER_SortList     = src/Examples/SortList/ProofSpecificationER

main_file_NER_Consistency = Test/Consistency/Readme

# Only used to publish the drafts, i.e. non type checking.
main_file_NER_Draft       = Draft/RenderToHTML

##############################################################################
# Type checking the agda files.

type_checking_NER_% :
	$(AGDA) ${main_file_NER_$*}.agda

type_checking_ER_% :
	$(AGDA) ${main_file_ER_$*}.agda

all_type_checking_NER : type_checking_NER_LTC \
			type_checking_NER_LTC-PCF \
			type_checking_NER_DivisionPCF \
			type_checking_NER_GCD \
			type_checking_NER_GCD-PCF \
			type_checking_NER_Logic \
			type_checking_NER_SortList \
			type_checking_NER_Consistency \

all_type_checking_ER  : type_checking_ER_LTC \
			type_checking_ER_LTC-PCF \
			type_checking_ER_DivisionPCF \
			type_checking_ER_GCD \
			type_checking_ER_GCD-PCF \
			type_checking_ER_SortList

all_type_checking     : all_type_checking_NER all_type_checking_ER

##############################################################################
# Test the conjecture files.

# Targets for conjectures in the examples.
conjectures_DivisionPCF : conjectures_Examples/DivisionPCF
conjectures_GCD         : conjectures_Examples/GCD
conjectures_GCD-PCF     : conjectures_Examples/GCD-PCF
conjectures_Logic       : conjectures_Examples/Logic
conjectures_SortList    : conjectures_Examples/SortList

# The time limit should be the maximum (--time=720) which is required
# by the postulate Examples.SortList.Closures.TreeOrdrightSubTree-TreeOrd.
# TODO: To use a variable for the find result
conjectures_Examples/% :
	for file in \
	  `find src/Examples/$*/ -name '*.agda' | xargs grep -l 'ATP prove'`; do \
	    rm -f /tmp/*.tptp; \
            if ! ( ${AGDA} $${file} ); then exit 1; fi; \
	    if ! ( ${AGDA2ATP} --time=180 $${file} ); then exit 1; fi; \
	done

# Process LTC and LTC-PCF conjectures.
# TODO: Merge with conjectures_Examples/%
conjectures_% :
	for file in `find src/$*/ -name '*.agda' | xargs grep -l 'ATP prove'`; do \
	    rm -f /tmp/*.tptp; \
            if ! ( ${AGDA} $${file} ); then exit 1; fi; \
	    if ! ( ${AGDA2ATP} --time=180 $${file} ); then exit 1; fi; \
	done

all_conjectures : conjectures_LTC \
		  conjectures_LTC_PCF \
                  conjectures_DivisionPCF \
		  conjectures_GCD \
		  conjectures_GCD_PCF \
		  conjectures_Logic \
		  conjectures_SortList

##############################################################################
# Consistency test

# Because we are using the option --unproved-conjecture-error we
# revert the agda2atp output.
all_consistency :
	for file in \
          `find Test/Consistency -name '*.agda' | xargs grep -l 'ATP prove'`; do \
	    rm -f /tmp/*.tptp; \
            if ! ( ${AGDA} $${file} ); then exit 1; fi; \
	    if ( ${AGDA2ATP} --time=10 $${file} ); then exit 1; fi; \
	done

##############################################################################
# Publish the .html files

# html_dir_XXX = /tmp/XXX/html/
# host_dir_XXX = $(root_host_dir)/XXX/

publish_% :
	rm -r -f /tmp/$*/html/
	$(AGDA) --html --html-dir=/tmp/$*/html/ ${main_file_NER_$*}.agda
	$(RSYNC) /tmp/$*/html/ $(root_host_dir)/$*/

all_publish : publish_LTC \
	      publish_LTC-PCF \
	      publish_DivisionPCF \
	      publish_GCD \
	      publish_GCD-PCF \
	      publish_Logic \
	      publish_SortList \
	      publish_Consistency

##############################################################################
# Other stuff

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp

##############################################################################
# Main

all_test : all_type_checking all_conjectures all_consistency

# TODO
# non_conjectures :
# 	./Test/non-conjectures.bash
