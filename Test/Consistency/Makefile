TOP = ../..
include $(TOP)/mk/config.mk

host_dir   = $(root_host_dir)/Consistency/
local_path = Test/Consistency
html_dir   = /tmp/$(local_path)/html/

# The conjectures are tested in every sub-directory (i.e. LTC,
# LTC-PCF, Examples/GCD, etc.).
# conjectures :

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/Readme.agda

type_checking_all : type_checking

publish :
	rm -r -f $(html_dir)

	cd $(TOP) && \
	$(AGDA) --html --html-dir=$(html_dir) $(local_path)/Readme.agda

	$(RSYNC) $(html_dir) $(host_dir)
