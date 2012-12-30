# Tested with:
# GNU Make 3.81 and
# GNU bash, version 4.2.8(1)-release (x86_64-pc-linux-gnu)

SHELL := /bin/bash

##############################################################################
# Paths

agda2atp_path       = src/agda2atp
dump-agdai_path     = src/dump-agdai
fix-whitespace_path = src/fix-whitespace
fot_path            = src/fot
peano_path          = src/peano

# Agda standard library path.
std_lib_path = ~/agda-upstream/std-lib

# Tests paths
errors_path        = $(agda2atp_path)/test/errors
non_theorems_path  = $(agda2atp_path)/test/non-theorems
options_path       = $(agda2atp_path)/test/options
theorems_path      = $(agda2atp_path)/test/theorems

# Directory for the TPTP files.
output_dir = /tmp/agda2atp

# Notes path.
notes_path = notes

# Snapshot fot directory.
snapshot_dir = snapshot-fot

##############################################################################
# Variables

agda2atp_haskell_files = $(shell find $(agda2atp_path)/src/ -name '*.hs')

AGDA = agda -v 0

# The defaults ATPs are e, equinox, and vampire.
AGDA2ATP = $(agda2atp_path)/dist/build/agda2atp/agda2atp
# AGDA2ATP = $(agda2atp_path)/dist/build/agda2atp/agda2atp --atp=e
# AGDA2ATP = $(agda2atp_path)/dist/build/agda2atp/agda2atp --atp=equinox
# AGDA2ATP = $(agda2atp_path)/dist/build/agda2atp/agda2atp --atp=ileancop
# AGDA2ATP = $(agda2atp_path)/dist/build/agda2atp/agda2atp --atp=metis
# AGDA2ATP = $(agda2atp_path)/dist/build/agda2atp/agda2atp --atp=spass
# AGDA2ATP = $(agda2atp_path)/dist/build/agda2atp/agda2atp --atp=vampire

##############################################################################
# Auxiliary functions

path_subst = $(patsubst %.agda,%.$(1), \
	     	$(shell find $(2) \( ! -path '*/Consistency/*' \) -name '*.agda' \
			| xargs grep -L 'The ATPs could not prove the theorem' \
			| xargs grep -l 'ATP prove' \
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

errors_files = $(call path_subst,errors,$(errors_path))

options_files = $(call path_subst,options,$(options_path))

# FOT

type_check_fot_files = \
  $(patsubst %.agda,%.type_check_fot, \
    $(shell find $(fot_path) -name 'Everything.agda' | sort))

type_check_agsy_fot_files = \
  $(patsubst %.agda,%.type_check_agsy_fot, \
    $(shell find $(fot_path)/Agsy/ -name '*.agda' | sort))

snapshot_create_fot_files = $(call path_subst,snapshot_create_fot,$(fot_path))

snapshot_compare_fot_files = \
  $(call path_subst,snapshot_compare_fot,$(fot_path))

prove_fot_files = $(call path_subst,prove_fot,$(fot_path))

consistency_fot_files = \
  $(patsubst %.agda,%.consistency_fot, \
    $(shell find $(fot_path) -path '*/Consistency/*' -name '*.agda' | sort))

# Notes

type_check_notes_files = \
  $(patsubst %.agda,%.type_check_notes, \
    $(shell find $(notes_path) -name '*.agda' | sort))

prove_notes_files = $(call path_subst,prove_notes,$(notes_path))

# Others

coq_type_check_files = $(patsubst %.v,%.coq_type_check, \
	               $(shell find -name '*.v' | sort))

benchmark_files = \
  $(fot_path)/FOTC/Base/PropertiesATP.benchmark \
  $(fot_path)/FOTC/Program/GCD/Partial/ProofSpecificationATP.benchmark \
  $(fot_path)/FOTC/Program/SortList/ProofSpecificationATP.benchmark

##############################################################################
# Test suite: Generated conjectures

flags_gt = -i$(theorems_path) --only-files \
	   --output-dir=$(output_dir)/$(theorems_path) \

%.generated_theorems :
	@echo "Processing $*.agda"
	@$(AGDA) -i$(theorems_path) $*.agda
	@$(AGDA2ATP) -v 0 $(flags_gt) $*.agda
	@diff -r $* $(output_dir)/$*

flags_ngt = -i$(non_theorems_path) --only-files \
	   --output-dir=$(output_dir)/$(non_theorems_path) \

%.generated_non_theorems :
	@echo "Processing $*.agda"
	@$(AGDA) -i$(non_theorems_path) $*.agda
	@$(AGDA2ATP) -v 0 $(flags_ngt) $*.agda
	@diff -r $* $(output_dir)/$*

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
# Test suite: Refute theorems

%.refute_theorems :
	@echo "Processing $*.agda"
	@$(AGDA) -i$(non_theorems_path) $*.agda
	@if ( $(AGDA2ATP) -i$(non_theorems_path) \
	                 --output-dir=$(output_dir) --time=5 $*.agda ); then \
	    exit 1; \
	fi

refute_theorems : $(refute_theorems_files)
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Options

%.options :
	@$(AGDA) -i$(options_path) $*.agda

# Tested with shelltest 1.3.1.
options : $(options_files)
	shelltest --color $(options_path)/options.test
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Error messages

%.errors :
	@$(AGDA) -i$(errors_path) $*.agda

# Tested with shelltest 1.3.1.
errors : $(errors_files)
	shelltest --color $(errors_path)/errors.test
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Haddock test

haddock_file = /tmp/haddock.tmp

doc :
	cd $(agda2atp_path) && cabal configure
	cd $(agda2atp_path) && cabal haddock --executables \
	                             --haddock-option=--use-unicode \
	                             --hyperlink-source  > $(haddock_file)
	cat $(haddock_file)
	diff <(find $(agda2atp_path)/src/ -name '*.hs' | wc -l) \
	     <(grep 100% $(haddock_file) | wc -l)
	@echo "$@ succeeded!"

##############################################################################
# FOT: Type-checking

%.type_check_fot :
	$(AGDA) -i$(fot_path) $*.agda

%.type_check_agsy_fot :
	$(AGDA) -i$(fot_path) -i $(std_lib_path)/src/ $*.agda

type_check_fot : $(type_check_fot_files) \
                 $(type_check_agsy_fot_files)
	$(AGDA) -i$(fot_path) $(fot_path)/README.agda
	@echo "$@ succeeded!"

##############################################################################
# FOT: Generated conjectures

# In FOT we use the snapshot_create_fot rule.

##############################################################################
# FOT: Snapshot

%.snapshot_create_fot :
	$(AGDA) -i$(fot_path) $*.agda
	$(AGDA2ATP) -i$(fot_path) --only-files --output-dir=$(snapshot_dir) $*.agda

%.snapshot_compare_fot :
	@echo "Processing $*.agda"
	@$(AGDA) -i$(fot_path) $*.agda
	@$(AGDA2ATP) -v 0 -i$(fot_path) --snapshot-test \
	            --snapshot-dir=$(snapshot_dir) $*.agda

snapshot_create_fot_aux : $(snapshot_create_fot_files)

snapshot_create_fot :
	rm -r -f $(snapshot_dir)
	make snapshot_create_fot_aux
	@echo "$@ succeeded!"

snapshot_compare_fot : $(snapshot_compare_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# FOT: Prove theorems

%.prove_fot :
	$(AGDA) -i$(fot_path) $*.agda
	$(AGDA2ATP) -i$(fot_path) --output-dir=$(output_dir) --time=240 $*.agda

prove_fot : $(prove_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# FOT: Consistency

%.consistency_fot :
	$(AGDA) -i$(fot_path) $*.agda
	if ( $(AGDA2ATP) -i$(fot_path) --output-dir=$(output_dir) \
	                 --time=10 $*.agda ); then \
           exit 1;\
        fi

consistency_fot : $(consistency_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# Notes: Type-checking

%.type_check_notes :
	$(AGDA) -i$(fot_path) \
                -i $(std_lib_path)/src/ \
	        -inotes \
	        -inotes/agda-interface \
	        -inotes/discrimination-rules \
	        -inotes/fixed-points \
                -inotes/papers/fossacs-2012 \
                -inotes/papers/paper-2011/ \
	        -inotes/README \
                -inotes/setoids \
	        -inotes/strictly-positive-inductive-types \
                -inotes/thesis \
                -inotes/type-classes \
	        $*.agda

type_check_notes : $(type_check_notes_files)
	@echo "$@ succeeded!"

##############################################################################
# Notes: Prove theorems

prove_notes_path = -i$(fot_path) \
                   -inotes \
                   -inotes/papers/fossacs-2012 \
                   -inotes/thesis/ \
                   -inotes/README

%.prove_notes :
	$(AGDA) $(prove_notes_path) $*.agda
	$(AGDA2ATP) $(prove_notes_path) --output-dir=$(output_dir) --time=240 $*.agda

prove_notes : $(prove_notes_files)
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to Agda

agda_changed : clean
	if [ ! -d $(snapshot_dir) ]; then \
	   echo "Error: The directory $(snapshot_dir) does not exist"; \
	   exit 1; \
	fi
	cd $(agda2atp_path) && cabal clean && cabal configure && cabal build
	make agda2atp_changed
	cd $(std_lib_path) && darcs pull
	make type_check_fot
	make snapshot_compare_fot
	make type_check_notes
	cd $(dump-agdai_path) && cabal clean && cabal configure && cabal build
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to agda2atp

agda2atp_changed :
	@make generated_conjectures
	@make errors
	@make options
	@make prove_notes
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a new ATP or a new version of an ATP

atp_changed :
	@make generated_conjectures
	@make prove_theorems
	@make refute_theorems
	@make errors
	@make options
	@make prove_notes
	@make prove_fot
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to Coq.

%.coq_type_check :
	coqc $*.v

coq_changed : coq_clean $(coq_type_check_files)
	@echo "$@ succeeded!"

coq_clean :
	rm -f *.glob *.vo

##############################################################################
# Test used when there is a modification to FOT.

fot_change :
	make type_check_fot
	make type_check_notes
	@echo "$@ succeeded!"

##############################################################################
# Hlint test

hlint :
	hlint $(agda2atp_path)/src/
	hlint $(dump-agdai_path)/src -i "Use on"
	hlint $(fix-whitespace_path)
	hlint $(peano_path)/src
	@echo "$@ succeeded!"

##############################################################################
# Git : pre-commit test

git_pre_commit :
	@fix-whitespace --check
	@make doc
	@make hlint
	@echo "$@ succeeded!"

##############################################################################
# Install

install :
	cd $(agda2atp_path) && cabal install
	cd $(dump-agdai_path) && cabal install
	cd $(fix-whitespace_path) && cabal install
	cd $(peano_path) && cabal install

##############################################################################
# Haskell program coverage

hpc_html_dir = $(agda2atp_path)/hpc

hpc : hpc_clean
	cd $(agda2atp_path) && cabal clean && cabal install --ghc-option=-fhpc
	make prove_theorems
	make refute_theorems
	make errors
	make options
	hpc markup --exclude=Paths_agda2atp \
	           --destdir=$(hpc_html_dir) \
	           --srcdir=$(agda2atp_path) \
                   agda2atp.tix
	hpc report --exclude=Paths_agda2atp \
                   --decl-list \
	           --srcdir=$(agda2atp_path) \
                   agda2atp.tix
	rm -f *.tix

hpc_clean :
	rm -f *.tix
	rm -f -r $(hpc_html_dir)

##############################################################################
# Benchmark

benchmark_tag = \
  $(shell echo `date +"%Y%m%d-%H.%M"`-ghc-`ghc --numeric-version`-`hostname -s`)

%.benchmark :
	$(AGDA) -i$(fot_path) $*.agda
	$(AGDA2ATP) -v 0 -i$(fot_path) $*.agda \
                   +RTS -s/tmp/benchmark/$(subst /,.,$*)

benchmark_aux : $(benchmark_files)

.PHONY : benchmark
benchmark :
	mkdir --parents /tmp/benchmark
	make benchmark_aux
	mkdir --parents $(agda2atp_path)/benchmark/$(benchmark_tag)
	mv /tmp/benchmark/* $(agda2atp_path)/benchmark/$(benchmark_tag)/
	@echo "$@ succeeded!"

##############################################################################
# Others

dependency_graph :
	$(AGDA) -i$(fot_path) \
	        --dependency-graph=/tmp/dependency-graph.gv \
	        $(fot_path)/FOTC/Program/ABP/ProofSpecificationATP.agda
	dot -Tpdf /tmp/dependency-graph.gv > /tmp/dependency-graph.pdf

.PHONY : TAGS
TAGS :
	hasktags -e $(agda2atp_haskell_files)

TODO :
	find -wholename './dist' -prune -o -print \
	| xargs grep -I 'TODO:' \
	| sort

clean :
	find -name '*.agdai' | xargs rm -f
	find -name '*.glob' | xargs rm -f
	find -name '*.hi' | xargs rm -f
	find -name '*.o' | xargs rm -f
	find -name '*.vo' | xargs rm -f
	find -name 'agda2atp.tix' | xargs rm -f
	find -name 'model' | xargs rm -f
	rm -f -r $(output_dir)
