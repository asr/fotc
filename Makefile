haskellFiles = $(shell find src/ -name '*.hs')

axiomsPath = Test/Succeed/OnlyAxioms
succeedPath = Test/Succeed
failPath = Test/Fail

axiomsTPTP = /tmp/axioms.tptp

axiomsFiles = $(patsubst %.agda,%,$(shell find $(axiomsPath) -name "*.agda"))

failConjectures = $(patsubst %.agda,%,$(shell find $(failPath) -name "*.agda"))

# We need avoid the files inside the $(axiomsPath) directory
succeedConjectures = $(patsubst %.agda,%, \
	$(shell find $(succeedPath) -path '$(axiomsPath)' -prune , -name "*.agda"))

AGDA = agda -v 0

TAGS : $(haskellFiles)
	hasktags -e $(haskellFiles)

$(axiomsFiles) : % : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi
	@if ! ( agda2atp --only-create-files $< ); then exit 1; fi
	@cat $@.ax | while read -r line; do \
		if ! ( grep --silent "$$line" $(axiomsTPTP) ) ; then \
			echo "Testing error. Translation to: $$line"; \
			exit 1; \
		fi \
	done

$(succeedConjectures) : % : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi
	@if ! ( agda2atp --time 60 $< ); then exit 1; fi

$(failConjectures) : % : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi
# The unproven conjectures return an error, therefore we wrapped it.
	@if ( agda2atp --time 5 $< ); then exit 1; fi

# The tests
axioms : clean $(axiomsFiles)
succeed : clean $(succeedConjectures)
fail : clean $(failConjectures)

test : axioms succeed fail

clean :
	find -name '*.agdai' | xargs rm -f
	rm -f /tmp/*.tptp
