haskell_files = $(shell find src/ -name '*.hs')
agda_files = $(shell find src/ -name '*.agda')
test_path = Test/Succeed
ATP = equinox

TAGS : $(haskell_files)
	hasktags -e $(haskell_files)

test : $(test_path)/Add.agda \
	$(test_path)/Hints.agda \
	$(test_path)/ImplicitArguments.agda \
	$(test_path)/LogicalConstants.agda \
	$(test_path)/Names.agda \
	$(test_path)/Where.agda \
	$(test_path)/RemoveQuantificationOverProofs.agda

	@for file in $^; \
	 do \
		make clean; \
		agda $$file; \
		agda-atp $$file; \
		find  /tmp/ -maxdepth 1 -name 'Test*.tptp' -execdir $(ATP) '{}' ';';\
	done

clean :
	@find -name '*.agdai' | xargs rm
	@rm -f /tmp/*.tptp
