# Tested with GNU Make 3.81

haskell_files = $(shell find src/ -name '*.hs')

AGDA = agda -v 0 --ignore-interfaces

# The defaults ATPs are e, equinox, and vampire.
AGDA2ATP = dist/build/agda2atp/agda2atp --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=e --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=equinox --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=metis --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=spass --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=vampire --output-dir=$(output_dir)

##############################################################################
# Some paths

succeed_path        = Test/Succeed
succeed_FOL_path    = $(succeed_path)/FOL
succeed_NonFOL_path = $(succeed_path)/NonFOL

# 2012-04-29: We don't have fail tests in NonFOL.
fail_FOL_path = Test/Fail

# Directory for the TPTP files.
output_dir = /tmp/agda2atp

##############################################################################
# Auxiliary functions

path_subst = $(patsubst %.agda,%.$(1), \
	     	$(shell find $(2) -name "*.agda" \
			| xargs grep -l 'ATP prove' \
		  	| sort))

##############################################################################
# Files

proved_conjectures_FOL_files = \
  $(call path_subst,proved_conjectures_FOL,$(succeed_FOL_path))

proved_conjectures_NonFOL_files = \
  $(call path_subst,proved_conjectures_NonFOL,$(succeed_NonFOL_path))

fail_FOL_files = $(call path_subst,fail_FOL,$(fail_FOL_path))

parsing_files = $(call path_subst,parsing,$(succeed_path))

generated_conjectures_files = \
  $(call path_subst,generated_conjectures,$(succeed_path))

snapshot_create_files = $(call path_subst,snapshot_create,$(succeed_path))

snapshot_test_files = $(call path_subst,snapshot_test,$(succeed_path))

##############################################################################

%.agdai : %.agda
	$(AGDA) $<

##############################################################################
# Proved conjectures test

%.proved_conjectures_FOL : %.agdai
	$(AGDA2ATP) --time=10 $*.agda

%.proved_conjectures_NonFOL : %.agdai
	$(AGDA2ATP) --time=10 --non-fol $*.agda

proved_conjectures : $(proved_conjectures_FOL_files) \
                     $(proved_conjectures_NonFOL_files)
	@echo "The $@ test succeeded!"

##############################################################################
# Fail test

%.fail_FOL : %.agdai
	if ( $(AGDA2ATP) --time=5 $*.agda ); then exit 1; fi

fail : $(fail_FOL_files)
	@echo "The $@ test succeeded!"

##############################################################################
# Generated conjectures test

%.generated_conjectures : %.agdai
	$(AGDA2ATP) --non-fol --only-files $*.agda
	diff -r $* $(output_dir)/$*

generated_conjectures : $(generated_conjectures_files)
	@echo "The $@ test succeeded!"

##############################################################################
# Parsing test

# We use tptp4X from the TPTP v5.4.0 to parse the TPTP files.
%.parsing : %.agdai
	$(AGDA2ATP) --non-fol --only-files $*.agda

	find $(output_dir) | while read file; do \
	  tptp4X $${file}; \
	done

	rm -r $(output_dir)
parsing : $(parsing_files)
	@echo "The $@ test succeeded!"

##############################################################################
# Snapshot of the succeed TPTP files

snapshot_dir = snapshot

%.snapshot_create : %.agdai
	agda2atp --only-files --non-fol --output-dir=$(snapshot_dir) $*.agda

%.snapshot_test : %.agdai
	agda2atp --non-fol --snapshot-test --snapshot-dir=$(snapshot_dir) $*.agda

snapshot_create : $(snapshot_create_files)
	@echo "The creation of the snapshot succeeded!"

snapshot_test : $(snapshot_test_files)
	@echo "The $@ test succeeded!"

snapshot_clean :
	rm -r -f $(snapshot_dir)

##############################################################################
# Haskell program coverage

hpc_html_dir = hpc

.PHONY : hpc
hpc : hpc_clean hpc_install \
      $(proved_conjectures_FOL_files) \
      $(proved_conjectures_NonFOL_files) \
      $(fail_FOL_files)
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
# Haddock test

doc :
	cabal configure
	cabal haddock --hyperlink-source \
                      --executables \
                      --haddock-option=--use-unicode
	@echo "The Haddock test succeeded!"

##############################################################################
# Running the tests

tests : clean
	@echo "======================================================================"
	@echo "== Suite of parsing tests ============================================"
	@echo "======================================================================"
	make parsing

	@echo "======================================================================"
	@echo "== Suite of generated conjectures tests =============================="
	@echo "======================================================================"
	make generated_conjectures

	@echo "======================================================================"
	@echo "== Suite of proved conjectures tests =================================="
	@echo "======================================================================"
	make proved_conjectures

	@echo "======================================================================"
	@echo "== Suite of failing tests ============================================"
	@echo "======================================================================"
	make fail

	@echo "======================================================================"
	@echo "== Testing the Haddock documentation =================================="
	@echo "======================================================================"
	make doc

	@echo "All tests succeeded!"

##############################################################################
# Others

.PHONY : TAGS
TAGS : $(haskell_files)
	hasktags -e $(haskell_files)

# Requires HLint >= 1.8.4.
hlint :
	hlint src/

.PHONY : TODO
TODO :
	find \( -name '*.hs' -o -name '*.hs-boot' -o -name '*.agda' \) \
	| xargs grep TODO \
        | sort

clean :
	rm -f -r $(output_dir)
