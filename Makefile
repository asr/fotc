# Tested with GNU Make 3.81

haskell_files = $(shell find src/ -name '*.hs')

AGDA     = agda -v 0
# The defaults ATPs are e, equinox, metis, spass, and vampire.
AGDA2ATP = agda2atp
# AGDA2ATP = agda2atp --atp=e
# AGDA2ATP = agda2atp --atp=equinox
# AGDA2ATP = agda2atp --atp=metis
# AGDA2ATP = agda2atp --atp=spass
# AGDA2ATP = agda2atp --atp=vampire

succeed_path = Test/Succeed
fail_path    = Test/Fail

snapshot_dir = snapshot

succeed_files = $(patsubst %.agda,%.succeed, \
	$(shell find $(succeed_path) -name "*.agda" | sort))

fail_files = $(patsubst %.agda,%.fail, \
	$(shell find $(fail_path) -name "*.agda" | sort))

parsing_files = $(patsubst %.agda,%.parsing, \
	$(shell find $(succeed_path) -name "*.agda" | sort))

snapshot_files_to_create = $(patsubst %.agda,%.snapshotcreate, \
	$(shell find $(succeed_path) -name "*.agda" | sort))

snapshot_files_to_test = $(patsubst %.agda,%.snapshottest, \
	$(shell find $(succeed_path) -name "*.agda" | sort))

%.agdai : %.agda
	@$(AGDA) $<

%.succeed : %.agdai
	@$(AGDA2ATP) --time=60 --unproved-conjecture-error $*.agda

%.fail : %.agdai
	@if ( $(AGDA2ATP) --time=5 \
                          --unproved-conjecture-error \
                          $*.agda ); then \
              exit 1; \
	fi

# Equinox has the better parser for TPTP files, so we use it to find problems.
%.parsing : %.agdai
	@echo "Parsing file" $*.agda
	@$(AGDA2ATP) --time=1 --atp=equinox $*.agda \
		      >/tmp/xxx.tmp 2>/tmp/parsing.error

	@if [ -s /tmp/parsing.error ]; then \
		echo "Parsing error in $${file}"; \
		exit 1; \
	fi; \

%.snapshotcreate : %.agdai
	@$(AGDA2ATP) --only-files --output-dir=$(snapshot_dir) $*.agda

%.snapshottest : %.agdai
	@$(AGDA2ATP) --snapshot-test --snapshot-dir=$(snapshot_dir) $*.agda

# Snapshot of the succeed TPTP files.
create_snapshot : $(snapshot_files_to_create)

# The tests
succeed  : $(succeed_files)
fail     : $(fail_files)
parsing  : $(parsing_files)
snapshot : $(snapshot_files_to_test)

test :
	@echo "======================================================================"
	@echo "== Testing the TPTP files ============================================"
	@echo "======================================================================"
	@make parsing

	@echo "======================================================================"
	@echo "== Suite of successfull tests ========================================"
	@echo "======================================================================"
	@make succeed

	@echo "======================================================================"
	@echo "== Suite of failing tests ============================================"
	@echo "======================================================================"
	@make fail

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
	find \( -name '*.hs' -o -name '*.agda' \) | xargs grep TODO | sort

clean :
	cabal clean
	rm -f /tmp/*.tptp
	rm -f TAGS

snapshot_clean :
	rm -r -f $(snapshot_dir)
