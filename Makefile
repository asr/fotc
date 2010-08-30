haskell_files = $(shell find src/ -name '*.hs')

non_conjectures_path = Test/Succeed/NonConjectures
succeed_path = Test/Succeed
fail_path = Test/Fail

general_roles_TPTP = /tmp/general-roles.tptp

non_conjectures_files = $(patsubst %.agda,%, \
	$(shell find $(non_conjectures_path) -name "*.agda"))

fail_conjectures = $(patsubst %.agda,%, \
	$(shell find $(fail_path) -name "*.agda"))

# We need avoid the files inside the $(non_conjectures_path) directory
succeed_conjectures = $(patsubst %.agda,%, \
	$(shell find $(succeed_path) -path '$(non_conjectures_path)' -prune , \
		     -name "*.agda"))
AGDA = agda -v 0
AGDA2ATP = agda2atp --atp=equinox --atp=eprover

TAGS : $(haskell_files)
	hasktags -e $(haskell_files)

$(non_conjectures_files) : % : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi
	@if ! ( agda2atp --only-files $< ); then exit 1; fi
	@cat $@.ax | while read -r line; do \
		if ! ( grep --silent "$$line" $(general_roles_TPTP) ) ; then \
			echo "Testing error. Translation to: $$line"; \
			exit 1; \
		fi \
	done

$(succeed_conjectures) : % : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi
	@if ! ( $(AGDA2ATP) --time 60 --unproved-error $< ); then \
		exit 1; \
	fi

$(fail_conjectures) : % : %.agda
	@if ! ( $(AGDA) $< ); then exit 1; fi
	@if ! ( $(AGDA2ATP) --time 5 $< ); then \
		exit 1; \
	fi

# The tests
non_conjectures : clean $(non_conjectures_files)
succeed : clean $(succeed_conjectures)
fail : clean $(fail_conjectures)

test : non_conjectures succeed fail

clean :
	find -name '*.agdai' | xargs rm -f
	rm -f /tmp/*.tptp
