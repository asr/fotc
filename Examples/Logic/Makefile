TOP = ../..
include $(TOP)/mk/config.mk

host_dir   = $(root_host_dir)/Logic/
local_path = Examples/Logic
html_dir   = /tmp/$(local_path)/html/

conjectures :
	cd $(TOP) && ./Test/conjectures.bash Logic

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/Logic.agda

type_checking_all : type_checking

all : type_checking_all conjectures

publish :
	rm -f $(html_dir)

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(html_dir) $(local_path)/Logic.agda

	$(RSYNC) $(html_dir) $(host_dir)
