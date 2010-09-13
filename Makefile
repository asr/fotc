haskell_files = $(shell find src/ -name '*.hs')

general_roles_TPTP = /tmp/general-roles.tptp

AGDA = agda -v 0
AGDA2ATP = agda2atp --atp=equinox --atp=eprover

succeed_conjectures_path = Test/Succeed/Conjectures
succeed_non_conjectures_path = Test/Succeed/NonConjectures

succeed_conjectures_files = $(patsubst %.agda,%, \
	$(shell find $(succeed_conjectures_path) -name "*.agda"))

succeed_non_conjectures_files = $(patsubst %.agda,%, \
	$(shell find $(succeed_non_conjectures_path) -name "*.agda"))

fail_path = Test/Fail

fail_files = $(patsubst %.agda,%, \
	$(shell find $(fail_path) -name "*.agda"))

$(succeed_non_conjectures_files) : % : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi
	@if ! ( agda2atp --only-files $< ); then exit 1; fi
	@cat $@.ax | while read -r line; do \
		if ! ( grep --silent "$$line" $(general_roles_TPTP) ) ; then \
			echo "Testing error. Translation to: $$line"; \
			exit 1; \
		fi \
	done

$(succeed_conjectures_files) : % : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi
	@if ! ( $(AGDA2ATP) --time 60 --unproved-conjecture-error $< ); then \
		exit 1; \
	fi

$(fail_files) : % : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi
	@if ! ( $(AGDA2ATP) --time 5 $< ); then \
		exit 1; \
	fi

# The tests
succeed_non_conjectures : clean $(succeed_non_conjectures_files)
succeed_conjectures : clean $(succeed_conjectures_files)
fail : clean $(fail_files)

test : succeed_non_conjectures succeed_conjectures fail

clean :
	find -name '*.agdai' | xargs rm -f
	rm -f /tmp/*.tptp

# The tags
TAGS : $(haskell_files)
	hasktags -e $(haskell_files)
