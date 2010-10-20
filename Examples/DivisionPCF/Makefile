TOP = ../..
include $(TOP)/mk/config.mk

host_dir   = $(root_host_dir)/Division/
local_path = Examples/DivisionPCF
html_dir   = /tmp/$(local_path)/html/

conjectures_PCF :
	cd $(TOP) && ./Test/conjectures.bash DivisionPCF

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/ProofSpecificationPCF.agda

type_checking_ER :
	cd $(TOP) && $(AGDA) $(local_path)/ProofSpecificationPCF-ER.agda

type_checking_all : type_checking_ER type_checking

all : type_checking_all conjectures_PCF

publish :
	rm -r -f $(html_dir)

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(html_dir) $(local_path)/ProofSpecificationPCF.agda

	$(RSYNC) $(html_dir) $(host_dir)
