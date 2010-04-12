haskellFiles = $(shell find src/ -name '*.hs')

conjecturesPath = Test/Succeed
axiomsPath = Test/Succeed/OnlyAxioms

axiomsTPTP = /tmp/axioms.tptp

axiomsFiles = $(patsubst %.agda,%,$(shell find $(axiomsPath) -name "*.agda"))

# We need avoid the files inside the $(axiomsPath) directory
conjecturesFiles = $(patsubst %.agda,%, \
	$(shell find $(conjecturesPath) -path '$(axiomsPath)' -prune , -name "*.agda"))

# ATP = eprover --tstp-format
ATP = equinox

AGDA = agda -v 0

TAGS : $(haskellFiles)
	hasktags -e $(haskellFiles)

$(axiomsFiles) : % : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi
	@if ! ( agda2atp $< ); then exit 1; fi
	@cat $@.ax | while read -r line; do \
		if ! ( grep --silent "$$line" $(axiomsTPTP) ) ; then \
			echo "Testing error. Translation to: $$line"; \
			exit 1; \
		fi \
	done

$(conjecturesFiles) : % : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi
	@if ! ( agda2atp $< ); then exit 1; fi
	@for file in /tmp/$(subst /,.,$@)*.tptp; do \
		${ATP} $${file} > $${file}.output; \
		if ! ( grep --silent "+++ RESULT: Theorem" $${file}.output ); then \
			echo "Testing error in file $${file}"; \
			exit 1; \
		fi \
	done

testAxioms : $(axiomsFiles)
testConjectures : $(conjecturesFiles)

test : testAxioms testConjectures

clean :
	find -name '*.agdai' | xargs rm -f
	rm -f /tmp/*.tptp /tmp/*.output
