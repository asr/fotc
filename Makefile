haskell_files = $(shell find src/ -name '*.hs')
agda_files = $(shell find src/ -name '*.agda')

TAGS : $(haskell_files)
	hasktags -e $(haskell_files)

test : Test/Add.agda Test/Where.agda Test/Hints.agda
	@for file in $^; \
	 do \
		make clean; \
		agda $$file; \
		agda-atp $$file; \
		find  /tmp/ -maxdepth 1 -name 'Test*.tptp' -execdir equinox '{}' ';';\
	done

clean :
	@rm -f Test/*.agdai
	@rm -f /tmp/*.tptp
