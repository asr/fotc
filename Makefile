src_files = $(shell find src/ -name '*.hs')

TAGS : $(src_files)
	hasktags -e $(src_files)

clean :
	rm -f test/*.agdai
	rm -f /tmp/*.tptp
