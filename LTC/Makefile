TOP = ..
include $(TOP)/mk/config.mk

host_dir   = $(root_host_dir)/LTC/
local_path = LTC
html_dir   = /tmp/$(local_path)/html/

consistency :
	cd $(TOP) && ./Test/consistency.bash LTC

conjectures :
	cd $(TOP) && ./Test/conjectures.bash LTC

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/Everything.agda

type_checking_ER :
	cd $(TOP) && $(AGDA) $(local_path)/EverythingER.agda

type_checking_all : type_checking_ER type_checking

all : type_checking_all conjectures

publish :
	rm -r -f $(html_dir)

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(html_dir) $(local_path)/Everything.agda

	$(RSYNC) $(html_dir) $(host_dir)
