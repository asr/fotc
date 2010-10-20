TOP = ../..
include $(TOP)/mk/config.mk

host_dir   = $(root_host_dir)/GCD/
local_path = Examples/GCD
html_dir   = /tmp/$(local_path)/html/

consistency :
	cd $(TOP) && ./Test/consistency.bash GCD

conjectures :
	cd $(TOP) && ./Test/conjectures.bash GCD

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/ProofSpecification.agda

type_checking_ER :
	cd $(TOP) && $(AGDA) $(local_path)/ProofSpecificationER.agda

type_checking_all : type_checking_ER type_checking

all : type_checking_all conjectures

publish :
	rm -r -f $(html_dir)

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(html_dir) $(local_path)/ProofSpecification.agda

	$(RSYNC) $(html_dir) $(host_dir)
