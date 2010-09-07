# Includes
TOP = ../..
include $(TOP)/mk/config.mk

host_dir = $(root_host_dir)/SortList/
local_path = Examples/SortList

conjectures :
	cd $(TOP) && ./test-conjectures.bash SortList

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/ProofSpecification.agda

type_checking_ER :
	cd $(TOP) && \
	$(AGDA) $(local_path)/Closures/ListER.agda && \
	$(AGDA) $(local_path)/PropertiesER.agda && \
	$(AGDA) $(local_path)/ProofSpecificationER.agda

type_checking_all : type_checking_ER type_checking

test : type_checking_all conjectures

publish :
	rm -r -f html/

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(local_path)/html \
		$(local_path)/ProofSpecification.agda

	$(RSYNC) html/ $(host_dir)
