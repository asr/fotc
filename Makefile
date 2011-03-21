haskell_files = $(shell find src/ -name '*.hs')

AGDA     = agda -v 0
AGDA2ATP = agda2atp  # The defaults ATPs are e, equinox, metis, and vampire.
# AGDA2ATP = agda2atp --atp=e
# AGDA2ATP = agda2atp --atp=equinox
# AGDA2ATP = agda2atp --atp=metis
# AGDA2ATP = agda2atp --atp=vampire

succeed_conjectures_path     = Test/Succeed/Conjectures
succeed_non_conjectures_path = Test/Succeed/NonConjectures
succeed_agda_path            = Test/Succeed/Agda
fail_path                    = Test/Fail

succeed_conjectures_files = $(patsubst %.agda,%, \
	$(shell find $(succeed_conjectures_path) -name "*.agda"))

succeed_non_conjectures_files = $(patsubst %.agda,%, \
	$(shell find $(succeed_non_conjectures_path) -name "*.agda"))

succeed_agda_files = $(patsubst %.agda,%, \
	$(shell find $(succeed_agda_path) -name "*.agda"))

fail_files = $(patsubst %.agda,%, \
	$(shell find $(fail_path) -name "*.agda"))

%.agdai : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi

# TODO: Test if the file *.ax exists.
# TODO: Is it possible to make this test in the conjecture files?
# $(succeed_non_conjectures_files) : % : %.agdai
# 	@if ! ( $(AGDA2ATP) --only-files $*.agda ); then exit 1; fi
# 	@cat $@.ax | while read -r line; do \
# 		if ! ( grep --silent "$$line" /tmp/$(subst /,.,$@).tptp ) ; then \
# 			echo "Testing error. Translation to: $$line"; \
# 			exit 1; \
# 		fi \
# 	done

$(succeed_non_conjectures_files) : % : %.agdai
	@if ! ( $(AGDA2ATP) --only-files $*.agda ); then exit 1; fi

$(succeed_conjectures_files) : % : %.agdai
	@if ! ( $(AGDA2ATP) --time=60 \
                            --unproved-conjecture-error \
                            $*.agda ); then \
		exit 1; \
	fi

$(succeed_agda_files) : % : %.agdai
	@if ! ( $(AGDA2ATP) --only-files $*.agda ); then exit 1; fi

$(fail_files) : % : %.agdai
	@if ( $(AGDA2ATP) --time=5 \
                          --unproved-conjecture-error \
                          $*.agda ); then \
              exit 1; \
	fi

# The tests
succeed_non_conjectures : $(succeed_non_conjectures_files)
succeed_conjectures     : $(succeed_conjectures_files)
succeed_agda            : $(succeed_agda_files)
fail                    : $(fail_files)

test : succeed_agda succeed_conjectures succeed_non_conjectures fail

##############################################################################
# Others

TAGS : $(haskell_files)
	hasktags -e $(haskell_files)

# Requires HLint >= 1.8.4.
hlint :
	hlint src/

doc :
	cabal configure
	cabal haddock --executables

.PHONY : TODO
TODO :
	@find \( -name '*.hs' -o -name '*.agda' \) | xargs grep TODO

clean :
	@find -name '*.agdai' | xargs rm -f
	@rm -f /tmp/*.tptp
