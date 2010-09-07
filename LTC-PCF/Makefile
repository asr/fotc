# Includes
TOP = ..
include $(TOP)/mk/config.mk

host_dir = $(root_host_dir)/LTC-PCF/
local_path = LTC-PCF

conjectures_PCF :
	cd $(TOP) && ./test-conjectures.bash LTC-PCF

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/Everything.agda

type_checking_ER :
	cd $(TOP) && $(AGDA) $(local_path)/EverythingER.agda

type_checking_all : type_checking_ER type_checking

test : type_checking_all conjectures_PCF

publish :
	rm -r -f html/

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(local_path)/html \
		$(local_path)/Everything.agda

	$(RSYNC) html/ $(host_dir)
