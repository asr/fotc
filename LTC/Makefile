# Includes
TOP = ..
include $(TOP)/mk/config.mk

host_dir = $(root_host_dir)/LTC/
local_path = LTC

consistency :
	cd $(TOP) && ./Test/consistency.bash LTC

conjectures :
	cd $(TOP) && ./Test/conjectures.bash LTC

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/Everything.agda

type_checking_ER :
	cd $(TOP) && $(AGDA) $(local_path)/EverythingER.agda

type_checking_all : type_checking_ER type_checking

test : type_checking_all conjectures

publish :
	rm -r -f html/

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(local_path)/html \
		$(local_path)/Everything.agda

	$(RSYNC) html/ $(host_dir)
