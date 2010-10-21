TOP = ..
include $(TOP)/mk/config.mk

host_dir   = $(root_host_dir)/Draft/
local_path = Draft
html_dir   = /tmp/$(local_path)/html/

publish :
	rm -r -f $(html_dir)

	cd $(TOP) && \
	$(AGDA) --no-termination-check --html --html-dir=$(html_dir) \
          $(local_path)/RenderToHTML.agda

	$(RSYNC) $(html_dir) $(host_dir)
