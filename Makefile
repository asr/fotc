# Tested with GNU Make 3.81

haskell_files = $(shell find src/ -name '*.hs')

AGDA     = agda -v 0
# The defaults ATPs are e, equinox, and vampire.
AGDA2ATP = agda2atp
# AGDA2ATP = agda2atp --atp=e
# AGDA2ATP = agda2atp --atp=equinox
# AGDA2ATP = agda2atp --atp=metis
# AGDA2ATP = agda2atp --atp=spass
# AGDA2ATP = agda2atp --atp=vampire

succeed_path        = Test/Succeed
succeed_path_FOL    = $(succeed_path)/FOL
succeed_path_NonFOL = $(succeed_path)/NonFOL

# 2012-04-29: We don't have fail tests in NonFOL
fail_path_FOL = Test/Fail

hpc_html_dir = hpc
output_dir   = /tmp/agda2atp
snapshot_dir = snapshot

succeed_files = $(patsubst %.agda,%.succeed, \
	$(shell find $(succeed_path) -name "*.agda" | sort))

succeed_files_FOL = $(patsubst %.agda,%.succeed_FOL, \
	$(shell find $(succeed_path_FOL) -name "*.agda" | sort))

succeed_files_NonFOL = $(patsubst %.agda,%.succeed_NonFOL, \
	$(shell find $(succeed_path_NonFOL) -name "*.agda" | sort))

fail_files_FOL = $(patsubst %.agda,%.fail_FOL, \
	$(shell find $(fail_path_FOL) -name "*.agda" | sort))

parsing_files = $(patsubst %.agda,%.parsing, \
	$(shell find $(succeed_path) -name "*.agda" | sort))

snapshot_files_to_create = $(patsubst %.agda,%.snapshotcreate, \
	$(shell find $(succeed_path) -name "*.agda" | sort))

snapshot_files_to_test = $(patsubst %.agda,%.snapshottest, \
	$(shell find $(succeed_path) -name "*.agda" | sort))

%.agdai : %.agda
	@$(AGDA) $<

%.succeed_FOL : %.agdai
	echo "Processing file $*.agda"
	@$(AGDA2ATP) --output-dir=$(output_dir) --time=60 $*.agda

%.succeed_NonFOL : %.agdai
	echo "Processing file $*.agda"
	@$(AGDA2ATP) --output-dir=$(output_dir) --time=60 --non-fol $*.agda

%.fail_FOL : %.agdai
	echo "Processing file $*.agda"
	@if ( $(AGDA2ATP) --output-dir=$(output_dir) --time=5 $*.agda ); then exit 1; fi

# Equinox has the better parser for TPTP files, so we use it to find problems.
%.parsing : %.agdai
	@echo "Parsing file" $*.agda
	@$(AGDA2ATP) --output-dir=$(output_dir) \
                     --time=1 \
                     --atp=equinox \
                     --non-fol \
                     $*.agda \
		      >/tmp/xxx.tmp 2>/tmp/parsing.error

	@if [ -s /tmp/parsing.error ]; then \
		echo "Parsing error in $${file}"; \
		exit 1; \
	fi; \

%.snapshotcreate : %.agdai
	@$(AGDA2ATP) --only-files \
                     --non-fol \
                     --output-dir=$(snapshot_dir) $*.agda

%.snapshottest : %.agdai
	@$(AGDA2ATP) --non-fol \
                     --snapshot-test \
                     --snapshot-dir=$(snapshot_dir) $*.agda

# Snapshot of the succeed TPTP files.
create_snapshot : $(snapshot_files_to_create)

# Haskell program coverage.
.PHONY : hpc
hpc : hpc_clean $(succeed_files_FOL) $(succeed_files_NonFOL) $(fail_files_FOL)
	hpc markup --destdir=$(hpc_html_dir) agda2atp
	hpc report --decl-list agda2atp

# The tests.
succeed  : $(succeed_files_FOL) $(succeed_files_NonFOL)
	@echo "The $@ test succeeded!"
fail     : $(fail_files_FOL)
	@echo "The $@ test succeeded!"
parsing  : $(parsing_files)
	@echo "The $@ test succeeded!"
snapshot : $(snapshot_files_to_test)
	@echo "The $@ test succeeded!"

test : clean
	@echo "======================================================================"
	@echo "== Suite of parsing tests ============================================"
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

	@echo "All tests succeeded!"

##############################################################################
# Others

doc:
	cabal configure
	cabal haddock --hyperlink-source --executables

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

snapshot_clean :
	rm -r -f $(snapshot_dir)

hpc_clean :
	rm -f *.tix
	rm -f -r $(hpc_html_dir)
