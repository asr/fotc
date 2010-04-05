haskell_files = $(shell find src/ -name '*.hs')
agda_files = $(shell find src/ -name '*.agda')

TAGS : $(haskell_files)
	hasktags -e $(haskell_files)

test : Test/Succeed/Add.agda \
	Test/Succeed/Hints.agda \
	Test/Succeed/ImplicitArguments.agda \
	Test/Succeed/LogicalConstants.agda \
	Test/Succeed/Names.agda \
	Test/Succeed/Where.agda \
	Test/Succeed/RemoveQuantificationOverProofs.agda

	@for file in $^; \
	 do \
		make clean; \
		agda $$file; \
		agda-atp $$file; \
		find  /tmp/ -maxdepth 1 -name 'Test*.tptp' -execdir equinox '{}' ';';\
	done

clean :
	@find -name '*.agdai' | xargs rm
	@rm -f /tmp/*.tptp
