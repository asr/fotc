TOP = ..
include $(TOP)/mk/config.mk

host_dir   = $(root_host_dir)/LTC-PCF/
local_path = LTC-PCF
html_dir   = /tmp/$(local_path)/html/

conjectures_PCF :
	cd $(TOP) && ./Test/conjectures.bash LTC-PCF

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/Everything.agda

type_checking_ER :
	cd $(TOP) && $(AGDA) $(local_path)/EverythingER.agda

type_checking_all : type_checking_ER type_checking

all : type_checking_all conjectures_PCF

publish :
	rm -r -f $(html_dir)

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(html_dir) $(local_path)/Everything.agda

	$(RSYNC) $(html_dir) $(host_dir)
