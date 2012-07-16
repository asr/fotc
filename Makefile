# Tested with GNU Make 3.81

SHELL := /bin/bash

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
theorems_path      = test/theorems
non_theorems_path  = test/non-theorems
error_path         = test/error

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

generated_theorems_files = \
  $(call path_subst,generated_theorems,$(theorems_path))

generated_non_theorems_files = \
  $(call path_subst,generated_non_theorems,$(non_theorems_path))

prove_theorems_files = $(call path_subst,prove_theorems,$(theorems_path))

refute_theorems_files = $(call path_subst,refute_theorems,$(non_theorems_path))

error_conjectures_files = $(call path_subst,error_conjectures,$(error_path))

parsing_conjectures_files = \
  $(call path_subst,parsing_conjectures,$(theorems_path))
parsing_conjectures_files += \
  $(call path_subst,parsing_conjectures,$(non_theorems_path))

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

flags_gt = -i$(theorems_path) --only-files \
	   --output-dir=$(output_dir)/$(theorems_path) \

%.generated_theorems :
	@echo "Processing $*.agda"
	$(AGDA) -i$(theorems_path) $*.agda
	$(AGDA2ATP) $(flags_gt) $*.agda; \

flags_ngt = -i$(non_theorems_path) --only-files \
	   --output-dir=$(output_dir)/$(non_theorems_path) \

%.generated_non_theorems :
	@echo "Processing $*.agda"
	$(AGDA) -i$(non_theorems_path) $*.agda
	$(AGDA2ATP) $(flags_ngt) $*.agda; \
	diff -r $* $(output_dir)/$*

generated_conjectures_aux : $(generated_theorems_files) \
	                    $(generated_non_theorems_files)

generated_conjectures :
	rm -r -f $(output_dir)
	make generated_conjectures_aux
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Prove theorems

%.prove_theorems :
	$(AGDA) -i$(theorems_path) $*.agda
	$(AGDA2ATP) -i$(theorems_path) --output-dir=$(output_dir) \
	            --time=10 $*.agda

prove_theorems : $(prove_theorems_files)
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Refute_theorems

%.refute_theorems :
	$(AGDA) -i$(non_theorems_path) $*.agda
	if ( $(AGDA2ATP) -i$(non_theorems_path) \
	                 --output-dir=$(output_dir) --time=5 $*.agda ); then \
	    exit 1; \
	fi

refute_theorems : $(refute_theorems_files)
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Error conjectures

%.error_conjectures :
	$(AGDA) -i$(error_path) $*.agda
	if ( $(AGDA2ATP) -i$(error_path) --only-files $*.agda ); then \
	    exit 1; \
	fi

error_conjectures : $(error_conjectures_files)
	@echo "$@ succeeded!"

##############################################################################
# Test suit: Parsing

flags_parsing = -i$(theorems_path) -i$(non_theorems_path)

# We use tptp4X from TPTP v5.4.0 to parse the TPTP files.
%.parsing_conjectures :
	$(AGDA) $(flags_parsing) $*.agda
	$(AGDA2ATP) $(flags_parsing) --only-files --output-dir=$(output_dir) \
	            $*.agda

	find $(output_dir) | while read file; do \
	  tptp4X $${file}; \
	done

parsing_conjectures_aux : $(parsing_conjectures_files)

parsing_conjectures :
	rm -r -f $(output_dir)
	make parsing_conjectures_aux
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Haddock test

doc :
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
	$(AGDA2ATP) -iexamples --only-files --output-dir=$(snapshot_dir) \
	            $*.agda

# We cannot use $(AGDA2ATP) due to the output directory.
%.snapshot_compare_examples :
	$(AGDA) -iexamples $*.agda
	$(AGDA2ATP) -iexamples --snapshot-test \
	            --snapshot-dir=$(snapshot_dir) $*.agda

snapshot_create_examples : $(snapshot_create_examples_files)
	@echo "$@ succeeded!"

snapshot_compare_examples : $(snapshot_compare_examples_files)
	@echo "$@ succeeded!"

##############################################################################
# Examples: Proved conjectures

%.proved_conjectures_examples :
	$(AGDA) -iexamples $*.agda
	$(AGDA2ATP) -iexamples --output-dir=$(output_dir) --time=240 $*.agda

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
	        -inotes/agda-interface \
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
	@make generated_conjectures
	@make prove_theorems
	@make refute_theorems
	@make error_conjectures
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
	cd utils/read-agda-interface \
	&& cabal clean && cabal configure && cabal build
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
	@make doc
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
	find -name 'model' | xargs rm -f
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
