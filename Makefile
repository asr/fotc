# Tested with GNU Make 3.81

haskell_files = $(shell find src/ -name '*.hs')

AGDA = agda -v 0

# The defaults ATPs are e, equinox, and vampire.
AGDA2ATP = dist/build/agda2atp/agda2atp
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=e
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=equinox
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=metis
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=spass
# AGDA2ATP = dist/build/agda2atp/agda2atp --atp=vampire

##############################################################################
# Some paths

# Agda standard library path.
std_lib_path = /home/asr/agda-upstream/std-lib

# Tests paths
proved_test_path         = test/proved
proved_test_fol_path     = $(proved_test_path)/fol
proved_test_non_fol_path = $(proved_test_path)/non-fol

non_proved_test_path     = test/non-proved
non_proved_test_fol_path = $(non_proved_test_path)/fol

# 2012-04-29: We don't have fail tests in non-fol.
fail_test_fol_path = test/fail/fol

# Directory for the TPTP files.
output_dir = /tmp/agda2atp

# Examples path
examples_path = examples

# Notes path
notes_path = notes

# Snapshot examples directory.
snapshot_dir = snapshot-examples

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

generated_proved_conjectures_test_fol_files = \
  $(call path_subst,generated_proved_conjectures_test_fol,$(proved_test_fol_path))

generated_proved_conjectures_test_non_fol_files = \
  $(call path_subst,generated_proved_conjectures_test_non_fol,$(proved_test_non_fol_path))

generated_non_proved_conjectures_test_fol_files = \
  $(call path_subst,generated_non_proved_conjectures_test_fol,$(non_proved_test_fol_path))

proved_conjectures_test_fol_files = \
  $(call path_subst,proved_conjectures_test_fol,$(proved_test_fol_path))

proved_conjectures_test_non_fol_files = \
  $(call path_subst,proved_conjectures_test_non_fol,$(proved_test_non_fol_path))

non_proved_conjectures_test_fol_files = \
  $(call path_subst,non_proved_conjectures_test_fol,$(non_proved_test_fol_path))

fail_test_fol_files = $(call path_subst,fail_test_fol,$(fail_test_fol_path))

parsing_test_files = $(call path_subst,parsing_test,$(proved_test_path))

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

%.generated_proved_conjectures_test_fol :
	$(AGDA) -i$(proved_test_fol_path) $*.agda
	$(AGDA2ATP) -i$(proved_test_fol_path) --only-files \
	              --output-dir=$(output_dir)/$(proved_test_fol_path) \
	              $*.agda
	diff -r $* $(output_dir)/$*

%.generated_proved_conjectures_test_non_fol :
	$(AGDA) -i$(proved_test_non_fol_path) $*.agda
	$(AGDA2ATP) -i$(proved_test_non_fol_path) --non-fol --only-files \
	              --output-dir=$(output_dir)/$(proved_test_non_fol_path) \
	              $*.agda
	diff -r $* $(output_dir)/$*

%.generated_non_proved_conjectures_test_fol :
	$(AGDA) -i$(non_proved_test_fol_path) $*.agda
	$(AGDA2ATP) -i$(non_proved_test_fol_path) --only-files \
	             --output-dir=$(output_dir)/$(non_proved_test_fol_path) \
	             $*.agda
	diff -r $* $(output_dir)/$*

generated_conjectures_test_aux : $(generated_proved_conjectures_test_fol_files) \
	                         $(generated_proved_conjectures_test_non_fol_files) \
	                         $(generated_non_proved_conjectures_test_fol_files) \

generated_conjectures_test :
	rm -r -f $(output_dir)
	make generated_conjectures_test_aux
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Proved conjectures

%.proved_conjectures_test_fol :
	$(AGDA) -i$(proved_test_fol_path) $*.agda
	$(AGDA2ATP) -i$(proved_test_fol_path) --output-dir=$(output_dir) \
	            --time=10 $*.agda

%.proved_conjectures_test_non_fol :
	$(AGDA) -i$(proved_test_non_fol_path) $*.agda
	$(AGDA2ATP) -i$(proved_test_non_fol_path) --non-fol \
	            --output-dir=$(output_dir) --time=10  $*.agda

proved_conjectures_test : $(proved_conjectures_test_fol_files) \
                          $(proved_conjectures_test_non_fol_files)
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Non-proved conjectures

%.non_proved_conjectures_test_fol :
	$(AGDA) -i$(non_proved_test_fol_path) $*.agda
	if ( $(AGDA2ATP) -i$(non_proved_test_fol_path) \
	                 --output-dir=$(output_dir) --time=5 $*.agda ); then \
	    exit 1; \
	fi

non_proved_conjectures_test : $(non_proved_conjectures_test_fol_files)
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Fail test

%.fail_test_fol :
	$(AGDA) -i$(fail_test_fol_path) $*.agda
	if ( $(AGDA2ATP) -i$(fail_test_fol_path) --only-files $*.agda ); then \
	    exit 1; \
	fi

fail_test : $(fail_test_fol_files)
	@echo "$@ succeeded!"

##############################################################################
# Test suit: Parsing

# We use tptp4X from TPTP v5.4.0 to parse the TPTP files.
%.parsing_test :
	$(AGDA) -i$(proved_test_fol_path) -i$(proved_test_non_fol_path) $*.agda
	$(AGDA2ATP) -i$(proved_test_fol_path) -i$(proved_test_non_fol_path) \
                    --non-fol --only-files --output-dir=$(output_dir) $*.agda

	find $(output_dir) | while read file; do \
	  tptp4X $${file}; \
	done

parsing_test_aux : $(parsing_test_files)

parsing_test : $(parsing_test_files)
	rm -r -f $(output_dir)
	make parsing_test_aux
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
	$(AGDA) -iexamples $*.agda

%.type_checking_agsy_examples :
	$(AGDA) -iexamples -i$(std_lib_path)/src/ $*.agda

type_checking_examples_aux : $(type_checking_examples_files) \
                             $(type_checking_agsy_examples_files)

type_checking_examples :
	cd $(std_lib_path) && darcs pull
	make type_checking_examples_aux
	$(AGDA) -iexamples examples/README.agda
	@echo "$@ succeeded!"

##############################################################################
# Examples: Generated conjectures

# In the examples we use the snapshot_create_examples rule.

##############################################################################
# Examples: Snapshot

# We cannot use $(AGDA2ATP) due to the output directory.
%.snapshot_create_examples :
	$(AGDA) -iexamples $*.agda
	$(AGDA2ATP) -iexamples --only-files --non-fol \
	            --output-dir=$(snapshot_dir) $*.agda

# We cannot use $(AGDA2ATP) due to the output directory.
%.snapshot_compare_examples :
	$(AGDA) -iexamples $*.agda
	$(AGDA2ATP) -iexamples --non-fol --snapshot-test \
	            --snapshot-dir=$(snapshot_dir) $*.agda

snapshot_create_examples : $(snapshot_create_examples_files)
	@echo "$@ succeeded!"

snapshot_compare_examples : $(snapshot_compare_examples_files)
	@echo "$@ succeeded!"

##############################################################################
# Examples: Proved conjectures

%.proved_conjectures_examples :
	$(AGDA) -iexamples $*.agda
	$(AGDA2ATP) -iexamples --non-fol --output-dir=$(output_dir) \
	            --time=240 $*.agda

proved_conjectures_examples : $(proved_conjectures_examples_files)
	@echo "$@ succeeded!"

##############################################################################
# Examples: Consistency

# Because we are using the option --unproved-conjecture-error we
# revert the agda2atp output.
%.consistency_examples :
	$(AGDA) -iexamples $*.agda
	if ( $(AGDA2ATP) -iexamples --output-dir=$(output_dir) \
	                 --time=10 $*.agda ); then \
           exit 1;\
        fi

consistency_examples : $(consistency_examples_files)
	@echo "$@ succeeded!"

##############################################################################
# Notes: Type-checking

%.type_checking_notes :
	$(AGDA) -iexamples \
	        -inotes \
	        -inotes/fixed-points \
                -inotes/papers/fossacs-2012 \
                -inotes/papers/paper-2011/ \
	        -inotes/README/ \
                -inotes/setoids/ \
                -inotes/thesis/logical-framework/ \
                -i$(std_lib_path)/src/ \
	        $*.agda

type_checking_notes_aux : $(type_checking_notes_files)

type_checking_notes :
	cd $(std_lib_path) && darcs pull
	make type_checking_notes_aux
	@echo "$@ succeeded!"

##############################################################################
# Running the tests

tests :
	@make generated_conjectures_test
	@make proved_conjectures_test
	@make non_proved_conjectures_test
	@make fail_test
	@echo "All tests succeeded!"

##############################################################################
# Running the examples and the notes

examples_and_notes :
	make type_checking_examples
	make snapshot_create_examples
	type_checking_notes
	@echo "Examples and notes succeeded!"

##############################################################################
# Test used when there is a modification to Agda

agda_changed :
	if [ ! -d $(snapshot_dir) ]; then exit 1; fi
	cabal clean && cabal configure && cabal build
	make tests
	make type_checking_examples
	make snapshot_compare_examples
	make type_checking_notes
	@echo "$@ succeeded!"

##############################################################################
# Hlint test

hlint :
	hlint src/

##############################################################################
# Git : pre-commit test

git-pre-commit :
	@fix-whitespace --check
	@cabal configure && cabal build
	@make tests
	@make haddock_test
	@make hlint
	@echo "$@ succeeded!"

##############################################################################
# Haskell program coverage

hpc_html_dir = hpc

.PHONY : hpc
hpc : hpc_clean hpc_install \
      $(proved_conjectures_test_fol_files) \
      $(proved_conjectures_test_non-fol_files) \
      $(fail_test_fol_files)
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
	$(AGDA) -iexamples --html --html-dir=/tmp/html/ examples/README.agda
	$(RSYNC) /tmp/html/ $(root_host_dir)/

##############################################################################
# Others

dependency_graph :
	$(AGDA) -iexamples \
	        --dependency-graph=/tmp/dependency-graph.gv \
	        examples/FOTC/Program/ABP/ProofSpecificationATP.agda
	dot -Tpdf /tmp/dependency-graph.gv > /tmp/dependency-graph.pdf

.PHONY : TAGS
TAGS : $(haskell_files)
	hasktags -e $(haskell_files)

TODO :
	find -wholename './dist' -prune -o -print \
	| xargs grep -I 'TODO:' \
	| sort

clean :
	find -name '*.agdai' | xargs rm -f
	rm -f -r $(output_dir) $(snapshot_dir)

##############################################################################
# TODO: From the Makefile in the old repository FOT

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
