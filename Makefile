haskell_files = $(shell find src/ -name '*.hs')
agda_files = $(shell find src/ -name '*.agda')

TAGS : $(haskell_files)
	hasktags -e $(haskell_files)

test : $(agda_files)
	@make clean
	agda Test/Add.agda
	agda-atp Test/Add.agda
	@find  /tmp/ -maxdepth 1 -name 'Test*.tptp' -execdir equinox '{}' ';'
	@make clean
	agda Test/Where.agda
	agda-atp Test/Where.agda
	@find  /tmp/ -maxdepth 1 -name 'Test*.tptp' -execdir equinox '{}' ';'

clean :
	@rm -f Test/*.agdai
	@rm -f /tmp/*.tptp
