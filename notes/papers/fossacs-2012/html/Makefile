include ~/code/utils/make/fossacs-2012/publish.mk

publish_html : index.html
	scp -P $(port) $< $(host_dir_html)
	linkchecker -r1 http://www1.eafit.edu.co/asicard/code/fossacs-2012/
