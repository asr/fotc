haskellFiles = $(shell find src/ -name '*.hs')

testPath = Test/Succeed
axiomsTestPath = $(testPath)/OnlyAxioms

axiomsFile = /tmp/axioms.tptp

ATP = equinox

TAGS : $(haskellFiles)
	hasktags -e $(haskellFiles)

axiomsTest : $(axiomsTestPath)/Hints.agda \
	$(axiomsTestPath)/InternalTypes.agda \
	$(axiomsTestPath)/RemoveQuantificationOverProofs.agda

	@for file in $(basename $^); do \
		if ! ( agda $$file.agda ) ; then \
			echo "Testing error: agda"; \
			exit 1; \
		fi; \
		if ! ( agda2atp $$file.agda ) ; then \
		 	echo "Testing error: agda2atp"; \
		  	exit 1; \
		fi; \
		cat $$file.test | while read -r line; do \
			if ! ( grep --silent "$$line" $(axiomsFile) ) ; then \
				echo "Testing error. Translation to: $$line"; \
		 		exit 1; \
		 	fi; \
		done \
	done

conjecturesTest : $(testPath)/Add.agda \
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
	make axiomsTest
	make conjecturesTest

clean :
	@find -name '*.agdai' | xargs rm
	@rm -f /tmp/*.tptp
