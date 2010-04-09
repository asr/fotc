haskellFiles = $(shell find src/ -name '*.hs')

conjecturesPath = Test/Succeed
axiomsPath = Test/Succeed/OnlyAxioms

axiomsTPTP = /tmp/axioms.tptp

axiomsFiles = $(patsubst %.agda,%,$(shell find $(axiomsPath) -name "*.agda"))

# We need avoid the files inside the $(axiomsPath) directory
conjecturesFiles = $(patsubst %.agda,%, \
	$(shell find $(conjecturesPath) -path '$(axiomsPath)' -prune , -name "*.agda"))

ATP = equinox

TAGS : $(haskellFiles)
	hasktags -e $(haskellFiles)

$(axiomsFiles) : % : %.agda
	@if ! ( agda $< ); then exit 1; fi
	@if ! ( agda2atp $< ); then exit 1; fi
	@cat $@.test | while read -r line; do \
		if ! ( grep --silent "$$line" $(axiomsTPTP) ) ; then \
			 echo "Testing error. Translation to: $$line"; \
			exit 1; \
		fi; \
	done

$(conjecturesFiles) : % : %.agda
	make clean
	@if ! ( agda $< ); then exit 1; fi
	@if ! ( agda2atp $< ); then exit 1; fi
	find  /tmp/ -maxdepth 1 -name 'Test*.tptp' -execdir $(ATP) '{}' ';'

axiomsTest : $(axiomsFiles)
conjecturesTest : $(conjecturesFiles)

allTests :
	make axiomsTest
	make conjecturesTest

clean :
	@find -name '*.agdai' | xargs rm
	@rm -f /tmp/*.tptp
