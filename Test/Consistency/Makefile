# Includes
TOP = ../..
include $(TOP)/mk/config.mk

host_dir = $(root_host_dir)/Consistency/
local_path = Test/Consistency

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/Readme.agda

type_checking_all : type_checking

publish :
	rm -r -f html/

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(local_path)/html \
		$(local_path)/Readme.agda

	$(RSYNC) html/ $(host_dir)
