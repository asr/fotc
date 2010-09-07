# Includes
TOP = ../..
include $(TOP)/mk/config.mk

host_dir = $(root_host_dir)/Logic/
local_path = Examples/Logic

conjectures :
	cd $(TOP) && ./test-conjectures.bash Logic

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/Logic.agda

type_checking_all : type_checking

test : type_checking_all conjectures

publish :
	rm -r -f html/

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(local_path)/html \
		$(local_path)/Logic.agda

	$(RSYNC) html/ $(host_dir)
