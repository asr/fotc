haskell_files = $(shell find src/ -name '*.hs')
agda_files = $(shell find src/ -name '*.agda')

TAGS : $(haskell_files)
	hasktags -e $(haskell_files)

test : $(agda_files) clean
	agda test/Add.agda
	agda-atp test/Add.agda
	find  /tmp/ -maxdepth 1 -name 'test*.tptp' -execdir equinox '{}' ';'
clean :
	rm -f test/*.agdai
	rm -f /tmp/*.tptp
