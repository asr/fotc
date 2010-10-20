TOP = ../..
include $(TOP)/mk/config.mk

host_dir   = $(root_host_dir)/SortList/
local_path = Examples/SortList
html_dir   = /tmp/$(local_path)/html/

consistency :
	cd $(TOP) && ./Test/consistency.bash SortList

conjectures :
	cd $(TOP) && ./Test/conjectures.bash SortList

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/ProofSpecification.agda

type_checking_ER :
	cd $(TOP) && \
	$(AGDA) $(local_path)/Closures/ListER.agda && \
	$(AGDA) $(local_path)/PropertiesER.agda && \
	$(AGDA) $(local_path)/ProofSpecificationER.agda

type_checking_all : type_checking_ER type_checking

all : type_checking_all conjectures

publish :
	rm -r -f $(html_dir)

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(html_dir) $(local_path)/ProofSpecification.agda

	$(RSYNC) $(html_dir) $(host_dir)
