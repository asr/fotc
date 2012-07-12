# Tested with GNU Make 3.81

haskell_files = $(shell find src/ -name '*.hs')

# The defaults ATPs are e, equinox, and vampire.
AGDA2ATP = dist/build/agda2atp/agda2atp --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=e --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=equinox --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=metis --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=spass --output-dir=$(output_dir)
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=vampire --output-dir=$(output_dir)

##############################################################################
# Some paths

# Agda standard library path.
std_lib_path = /home/asr/agda-upstream/std-lib

# Tests paths
succeed_test_path        = Test/Succeed
succeed_test_FOL_path    = $(succeed_test_path)/FOL
succeed_test_NonFOL_path = $(succeed_test_path)/NonFOL

# 2012-04-29: We don't have fail tests in NonFOL.
fail_test_FOL_path = Test/Fail

# Directory for the TPTP files.
output_dir = /tmp/agda2atp

# Examples path
examples_path = examples

# Notes path
notes_path = notes

# Snapshot directory.
snapshot_dir = snapshot

##############################################################################
# Auxiliary functions

path_subst = $(patsubst %.agda,%.$(1), \
	     	$(shell find $(2) -name '*.agda' \
			| xargs grep -l 'ATP prove' \
                        | xargs grep -L 'ConsistencyTest' \
		  	| sort))

##############################################################################
# Files

# Tests

generated_conjectures_test_files = \
  $(call path_subst,generated_conjectures_test,$(succeed_test_path))

proved_conjectures_test_FOL_files = \
  $(call path_subst,proved_conjectures_test_FOL,$(succeed_test_FOL_path))

proved_conjectures_test_NonFOL_files = \
  $(call path_subst,proved_conjectures_test_NonFOL,$(succeed_test_NonFOL_path))

fail_test_FOL_files = $(call path_subst,fail_test_FOL,$(fail_test_FOL_path))

parsing_test_files = $(call path_subst,parsing,$(succeed_test_path))

# Examples

type_checking_examples_files = \
  $(patsubst %.agda,%.type_checking_examples, \
    $(shell find $(examples_path) -name 'Everything.agda' | sort))

type_checking_agsy_examples_files = \
  $(patsubst %.agda,%.type_checking_agsy_examples, \
    $(shell find $(examples_path)/Agsy -name '*.agda' | sort))

snapshot_create_examples_files = \
  $(call path_subst,snapshot_create_examples,$(examples_path))

snapshot_compare_examples_files = \
  $(call path_subst,snapshot_compare_examples,$(examples_path))

proved_conjectures_examples_files = \
  $(call path_subst,proved_conjectures_examples,$(examples_path))

consistency_examples_files = \
  $(patsubst %.agda,%.consistency_examples, \
    $(shell find $(examples_path) -name '*ConsistencyTest.agda' | sort))

# Notes

type_checking_notes_files = \
  $(patsubst %.agda,%.type_checking_notes, \
    $(shell find $(notes_path) -name '*.agda' | sort))

##############################################################################
# Test suite: Generated conjectures

%.generated_conjectures_test :
	agda -v 0 $*.agda
	$(AGDA2ATP) --non-fol --only-files $*.agda
	diff -r $* $(output_dir)/$*

generated_conjectures_test : $(generated_conjectures_test_files)
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Proved conjectures

%.proved_conjectures_test_FOL :
	agda -v 0 $*.agda
	$(AGDA2ATP) --time=10 $*.agda

%.proved_conjectures_test_NonFOL :
	agda -v 0 $*.agda
	$(AGDA2ATP) --time=10 --non-fol $*.agda

proved_conjectures_test : $(proved_conjectures_test_FOL_files) \
                          $(proved_conjectures_test_NonFOL_files)
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Fail test

%.fail_test_FOL :
	agda -v 0 $*.agda
	if ( $(AGDA2ATP) --time=5 $*.agda ); then exit 1; fi

fail_test : $(fail_test_FOL_files)
	@echo "$@ succeeded!"

##############################################################################
# Test suit: Parsing

# We use tptp4X from TPTP v5.4.0 to parse the TPTP files.
%.parsing_test :
	agda -v 0 $*.agda
	$(AGDA2ATP) --non-fol --only-files $*.agda

	find $(output_dir) | while read file; do \
	  tptp4X $${file}; \
	done

	rm -r $(output_dir)
parsing_test : $(parsing_test_files)
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Haddock test

haddock_test :
	cabal configure
	cabal haddock --hyperlink-source \
                      --executables \
                      --haddock-option=--use-unicode
	@echo "The Haddock test succeeded!"

##############################################################################
# Examples: Type-checking

%.type_checking_examples :
	agda -v 0 -iexamples $*.agda

%.type_checking_agsy_examples :
	agda -v 0 -iexamples -i$(std_lib_path)/src/ $*.agda

type_checking_examples_aux : $(type_checking_examples_files) \
                             $(type_checking_agsy_examples_files)

type_checking_examples :
	cd $(std_lib_path) && darcs pull
	make type_checking_examples_aux
	agda -v 0 -iexamples examples/README.agda
	@echo "$@ succeeded!"

##############################################################################
# Examples: Generated conjectures

# In the examples we use the snapshot_create_examples rule.

##############################################################################
# Examples: Snapshot

# We cannot use $(AGDA2ATP) due to the output directory.
%.snapshot_create_examples :
	agda -v 0 -iexamples $*.agda
	dist/build/agda2atp/agda2atp -iexamples --only-files --non-fol \
	                             --output-dir=$(snapshot_dir) $*.agda

# We cannot use $(AGDA2ATP) due to the output directory.
%.snapshot_compare_examples :
	agda -v 0 -iexamples $*.agda
	dist/build/agda2atp/agda2atp -iexamples --non-fol --snapshot-test \
	                             --snapshot-dir=$(snapshot_dir) $*.agda

snapshot_create_examples : $(snapshot_create_examples_files)
	@echo "$@ succeeded!"

snapshot_compare_examples : $(snapshot_compare_examples_files)
	@echo "$@ succeeded!"

##############################################################################
# Examples: Proved conjectures

%.proved_conjectures_examples :
	agda -v 0 -iexamples $*.agda
	$(AGDA2ATP) -iexamples --non-fol --time=240 $*.agda

proved_conjectures_examples : $(proved_conjectures_examples_files)
	@echo "$@ succeeded!"

##############################################################################
# Examples: Consistency

# Because we are using the option --unproved-conjecture-error we
# revert the agda2atp output.
%.consistency_examples :
	agda -v 0 -iexamples $*.agda
	if ( $(AGDA2ATP) -iexamples --time=10 $*.agda ); then exit 1; fi

consistency_examples : $(consistency_examples_files)
	@echo "$@ succeeded!"

##############################################################################
# Notes: Type-checking

%.type_checking_notes :
	agda -v 0 \
	     -iexamples \
	     -inotes \
	     -inotes/fixed-points \
             -inotes/papers/fossacs-2012 \
             -inotes/papers/paper-2011/ \
	     -inotes/README/ \
             -inotes/setoids/ \
             -inotes/thesis/logical-framework/ \
	     -inotes/TODO/ \
             -i$(std_lib_path)/src/ \
	     $*.agda

type_checking_notes_aux : $(type_checking_notes_files)

type_checking_notes :
	cd $(std_lib_path) && darcs pull
	make type_checking_notes_aux
	@echo "$@ succeeded!"

##############################################################################
# Running the tests

tests : clean
	make generated_conjectures_test
	make proved_conjectures_test
	make fail_test
	make haddock_test
	@echo "All tests succeeded!"

##############################################################################
# Running the examples and the notes

examples_and_notes : clean
	make type_checking_examples
	make snapshot_create_examples
	type_checking_notes
	@echo "Examples and notes succeeded!"

##############################################################################
# Haskell program coverage

hpc_html_dir = hpc

.PHONY : hpc
hpc : hpc_clean hpc_install \
      $(proved_conjectures__test_FOL_files) \
      $(proved_conjectures_test_NonFOL_files) \
      $(fail_test_FOL_files)
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
# Examples: Publishing the .html files

include ~/code/utils/make/agda2atp/publish.mk

publish_README :
	rm -r -f /tmp/html/
	agda -v 0 -iexamples --html --html-dir=/tmp/html/ examples/README.agda
	$(RSYNC) /tmp/html/ $(root_host_dir)/

##############################################################################
# Others

.PHONY : TAGS
TAGS : $(haskell_files)
	hasktags -e $(haskell_files)

# Requires HLint >= 1.8.4.
hlint :
	hlint src/

TODO :
	find -wholename './dist' -prune -o -print \
	| xargs grep -I 'TODO:' \
	| sort

clean :
	find -name '*.agdai' | xargs rm -f
	rm -f -r $(output_dir) $(snapshot_dir)

##############################################################################
# TODO: From the Makefile in the old repository FOT

# Test used when there is a modification to Agda

# agda_changed : agda_changed_clean all_type_checking all_only_conjectures
# 	@echo "The $@ test succeeded!"

# agda_changed_clean :
# 	find -name '*.agdai' | xargs rm -f

# Publish the .html files

# publish_note :
# 	$(RSYNC) html/ $(root_host_dir)/notes/
# 	rm -r html

# publish_Agsy : $(Agsy_files)
# 	rm -r -f /tmp/Agsy/html/
# 	for file in $(Agsy_files); do \
# 	  $(AGDA_Agsy) --html --html-dir=/tmp/Agsy/html/ $${file}; \
# 	done
# 	$(RSYNC) /tmp/Agsy/html/ $(root_host_dir)/Agsy/

# Other stuff

# dependency_graph : FOTC/Program/GCD/Total/ProofSpecificationATP.agda
# 	$(AGDA_FOT) --dependency-graph=/tmp/dependency-graph-gcd.gv $<
# 	dot -Tps /tmp/dependency-graph-gcd.gv > /tmp/dependency-graph-gcd.ps
