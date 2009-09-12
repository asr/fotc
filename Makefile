src_files = $(shell find src/ -name '*.hs')

TAGS : $(src_files)
	hTags -e $(src_files)

clean :
	rm -f test/*.agdai
