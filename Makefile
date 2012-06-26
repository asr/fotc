# Tested with GNU Make 3.81

haskell_files = $(shell find src/ -name '*.hs')

AGDA = agda -v 0

# The defaults ATPs are e, equinox, and vampire.
AGDA2ATP = dist/build/agda2atp/agda2atp --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=e --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=equinox --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=metis --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=spass --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=vampire --output-dir=$(output_dir)

succeed_path        = Test/Succeed
succeed_path_FOL    = $(succeed_path)/FOL
succeed_path_NonFOL = $(succeed_path)/NonFOL

# 2012-04-29: We don't have fail tests in NonFOL
fail_path_FOL = Test/Fail

output_dir   = /tmp/agda2atp

succeed_files = $(patsubst %.agda,%.succeed, \
	$(shell find $(succeed_path) -name "*.agda" | sort))

succeed_files_FOL = $(patsubst %.agda,%.succeed_FOL, \
	$(shell find $(succeed_path_FOL) -name "*.agda" | sort))

succeed_files_NonFOL = $(patsubst %.agda,%.succeed_NonFOL, \
	$(shell find $(succeed_path_NonFOL) -name "*.agda" | sort))

fail_files_FOL = $(patsubst %.agda,%.fail_FOL, \
	$(shell find $(fail_path_FOL) -name "*.agda" | sort))

parsing_files = $(patsubst %.agda,%.parsing, \
	$(shell find $(succeed_path) -name "*.agda" | \
                     xargs grep -l 'ATP prove' | \
                sort))

snapshot_files_to_create = $(patsubst %.agda,%.snapshotcreate, \
	$(shell find $(succeed_path) -name "*.agda" | sort))

snapshot_files_to_test = $(patsubst %.agda,%.snapshottest, \
	$(shell find $(succeed_path) -name "*.agda" | sort))

%.agdai : %.agda
	$(AGDA) $<

##############################################################################
# Succeed test.

%.succeed_FOL : %.agdai
	$(AGDA2ATP) --time=10 $*.agda

%.succeed_NonFOL : %.agdai
	$(AGDA2ATP) --time=10 --non-fol $*.agda

succeed  : $(succeed_files_FOL) $(succeed_files_NonFOL)
	@echo "The $@ test succeeded!"

##############################################################################
# Fail test.

%.fail_FOL : %.agdai
	if ( $(AGDA2ATP) --time=5 $*.agda ); then exit 1; fi

fail : $(fail_files_FOL)
	@echo "The $@ test succeeded!"

##############################################################################
# Parsing test.

# We use tptp4X from the TPTP library to parse the TPTP files.
%.parsing : %.agdai
	$(AGDA2ATP) --non-fol --only-files $*.agda

	find $(output_dir) | while read file; do \
	  tptp4X $${file}; \
	done

	rm -r $(output_dir)
parsing  : $(parsing_files)
	@echo "The $@ test succeeded!"

##############################################################################
# Snapshot of the succeed TPTP files.

snapshot_dir = snapshot

%.snapshotcreate : %.agdai
	agda2atp --only-files --non-fol --output-dir=$(snapshot_dir) $*.agda

%.snapshottest : %.agdai
	agda2atp --non-fol --snapshot-test --snapshot-dir=$(snapshot_dir) $*.agda

create_snapshot : $(snapshot_files_to_create)
	@echo "The creation of the snapshot succeeded!"

snapshot : $(snapshot_files_to_test)
	@echo "The $@ test succeeded!"

snapshot_clean :
	rm -r -f $(snapshot_dir)

##############################################################################
# Haskell program coverage.

hpc_html_dir = hpc

.PHONY : hpc
hpc : hpc_clean hpc_install \
      $(succeed_files_FOL) $(succeed_files_NonFOL) $(fail_files_FOL)
	hpc markup --exclude=Snapshot \
                   --exclude=Paths_agda2atp \
                   --destdir=$(hpc_html_dir) \
                   agda2atp
	hpc report --exclude=Snapshot \
                   --exclude=Paths_agda2atp \
                   --decl-list \
                   agda2atp
hpc_install :
	cabal clean && cabal install --ghc-option=-fhpc

hpc_clean :
	rm -f *.tix
	rm -f -r $(hpc_html_dir)

##############################################################################
# Running the tests.
test : clean
	@echo "======================================================================"
	@echo "== Suite of parsing tests ============================================"
	@echo "======================================================================"
	make parsing

	@echo "======================================================================"
	@echo "== Suite of successfull tests ========================================"
	@echo "======================================================================"
	make succeed

	@echo "======================================================================"
	@echo "== Suite of failing tests ============================================"
	@echo "======================================================================"
	make fail

	@echo "All tests succeeded!"

##############################################################################
# Others

doc:
	cabal configure
	cabal haddock --hyperlink-source \
                      --executables \
                      --haddock-option=--use-unicode

.PHONY : TAGS
TAGS : $(haskell_files)
	hasktags -e $(haskell_files)

# Requires HLint >= 1.8.4.
hlint :
	hlint src/

.PHONY : TODO
TODO :
	find \( -name '*.hs' -o -name '*.hs-boot' -o -name '*.agda' \) \
	| xargs grep TODO | sort

clean :
	find -name '*.agdai' | xargs rm -f
	rm -f -r $(output_dir)
	rm -f TAGS
