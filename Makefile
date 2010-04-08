haskellFiles = $(shell find src/ -name '*.hs')

testPath = Test/Succeed
testAxiomsPath = $(testPath)/OnlyAxioms

axiomsFile = /tmp/axioms.tptp

ATP = equinox

TAGS : $(haskellFiles)
	hasktags -e $(haskellFiles)

testAxioms : $(testAxiomsPath)/Hints.agda \
	$(testAxiomsPath)/InternalTypes.agda \
	$(testAxiomsPath)/RemoveQuantificationOverProofs.agda

	@for file in $(basename $^); do \
		agda $$file.agda; \
		if [ $$? != 0 ]; then \
			echo "Testing error: agda"; \
			exit 1; \
		fi; \
		agda2atp $$file.agda; \
		if [ $$? != 0 ]; then \
		 	echo "Testing error: agda2atp"; \
		  	exit 1; \
		fi; \
		cat $$file.test | while read -r line; do \
			grep --silent "$$line" $(axiomsFile); \
			if [ $$? != 0 ]; then \
				echo "Testing error. Translation to: $$line"; \
		 		exit 1; \
		 	fi; \
		done; \
	done

testConjectures : $(testPath)/Add.agda \
	$(testPath)/ImplicitArguments.agda \
	$(testPath)/LogicalConstants.agda \
	$(testPath)/Names.agda \
	$(testPath)/VariableNamesClash.agda \
	$(testPath)/Where.agda \

	@for file in $^; \
	 do \
		make clean; \
		agda $$file; \
		agda2atp $$file; \
		find  /tmp/ -maxdepth 1 -name 'Test*.tptp' -execdir $(ATP) '{}' ';';\
	done

allTests :
	make testAxioms
	make testConjectures

clean :
	@find -name '*.agdai' | xargs rm
	@rm -f /tmp/*.tptp
