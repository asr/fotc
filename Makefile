# Tested with:
# GNU Make 3.81 and
# GNU bash, version 4.2.8(1)-release (x86_64-pc-linux-gnu)

SHELL := /bin/bash

agda2atp_haskell_files = $(shell find agda2atp/src/ -name '*.hs')

AGDA = agda -v 0

# The defaults ATPs are e, equinox, and vampire.
AGDA2ATP = agda2atp/dist/build/agda2atp/agda2atp
# AGDA2ATP = agda2atp/dist/build/agda2atp/agda2atp --atp=e
# AGDA2ATP = agda2atp/dist/build/agda2atp/agda2atp --atp=equinox
# AGDA2ATP = agda2atp/dist/build/agda2atp/agda2atp --atp=metis
# AGDA2ATP = agda2atp/dist/build/agda2atp/agda2atp --atp=spass
# AGDA2ATP = agda2atp/dist/build/agda2atp/agda2atp --atp=vampire

##############################################################################
# Some paths

# Agda standard library path.
std_lib_path = ~/agda-upstream/std-lib

# Tests paths
errors_path        = test/errors
non_theorems_path  = test/non-theorems
options_path       = test/options
theorems_path      = test/theorems

# Directory for the TPTP files.
output_dir = /tmp/agda2atp

# FOT path
fot_path = fot

# Notes path
notes_path = notes

# Snapshot fot directory.
snapshot_dir = snapshot-fot

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

errors_files = $(call path_subst,errors,$(errors_path))

options_files = $(call path_subst,options,$(options_path))

parsing_conjectures_files = \
  $(call path_subst,parsing_conjectures,$(theorems_path))
parsing_conjectures_files += \
  $(call path_subst,parsing_conjectures,$(non_theorems_path))

# FOT

type_check_fot_files = \
  $(patsubst %.agda,%.type_check_fot, \
    $(shell find fot/ -name 'Everything.agda' | sort))

type_check_agsy_fot_files = \
  $(patsubst %.agda,%.type_check_agsy_fot, \
    $(shell find fot/Agsy/ -name '*.agda' | sort))

snapshot_create_fot_files = $(call path_subst,snapshot_create_fot,fot)

snapshot_compare_fot_files = $(call path_subst,snapshot_compare_fot,fot)

prove_fot_files = $(call path_subst,prove_fot,fot)

consistency_fot_files = \
  $(patsubst %.agda,%.consistency_fot, \
    $(shell find fot/ -name '*ConsistencyTest.agda' | sort))

# Notes

type_check_notes_files = \
  $(patsubst %.agda,%.type_check_notes, \
    $(shell find $(notes_path) -name '*.agda' | sort))

# Others

coq_type_check_files = $(patsubst %.v,%.coq_type_check, \
	               $(shell find -name '*.v' | sort))

benchmark_files = fot/FOTC/Base/PropertiesATP.benchmark \
                  fot/FOTC/Program/GCD/Partial/ProofSpecificationATP.benchmark \
                  fot/FOTC/Program/SortList/ProofSpecificationATP.benchmark

##############################################################################
# Test suite: Generated conjectures

flags_gt = -i$(theorems_path) --only-files \
	   --output-dir=$(output_dir)/$(theorems_path) \

%.generated_theorems :
	@echo "Processing $*.agda"
	@$(AGDA) -i$(theorems_path) $*.agda
	@$(AGDA2ATP) -v 0 $(flags_gt) $*.agda; \
	diff -r $* $(output_dir)/$*

flags_ngt = -i$(non_theorems_path) --only-files \
	   --output-dir=$(output_dir)/$(non_theorems_path) \

%.generated_non_theorems :
	@echo "Processing $*.agda"
	@$(AGDA) -i$(non_theorems_path) $*.agda
	@$(AGDA2ATP) -v 0 $(flags_ngt) $*.agda; \
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

options : $(options_files)
	shelltest $(options_path)/options.test
	@echo "$@ succeeded!"

##############################################################################
# Test suite: Error messages

%.errors :
	@$(AGDA) -i$(errors_path) $*.agda

errors : $(errors_files)
	shelltest $(errors_path)/errors.test
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

haddock_file = /tmp/haddock.tmp

doc :
	cd agda2atp && cabal configure
	cd agda2atp && cabal haddock --executables \
	                             --haddock-option=--use-unicode \
	                             --hyperlink-source  > $(haddock_file)
	cat $(haddock_file)
	diff <(find agda2atp/src/ -name '*.hs' | wc -l) <(grep 100% $(haddock_file) | wc -l)
	@echo "$@ succeeded!"

##############################################################################
# FOT: Type-checking

%.type_check_fot :
	$(AGDA) -ifot $*.agda

%.type_check_agsy_fot :
	$(AGDA) -ifot -i $(std_lib_path)/src/ $*.agda

type_check_fot_aux : $(type_check_fot_files) \
                     $(type_check_agsy_fot_files)

type_check_fot :
	cd $(std_lib_path) && darcs pull
	make type_check_fot_aux
	$(AGDA) -ifot fot/README.agda
	@echo "$@ succeeded!"

##############################################################################
# FOT: Generated conjectures

# In the FOT we use the snapshot_create_fot rule.

##############################################################################
# FOT: Snapshot

# We cannot use $(AGDA2ATP) due to the output directory.
%.snapshot_create_fot :
	$(AGDA) -ifot $*.agda
	$(AGDA2ATP) -ifot --only-files --output-dir=$(snapshot_dir) $*.agda

# We cannot use $(AGDA2ATP) due to the output directory.
%.snapshot_compare_fot :
	@echo "Processing $*.agda"
	@$(AGDA) -ifot $*.agda
	@$(AGDA2ATP) -v 0 -ifot --snapshot-test \
	            --snapshot-dir=$(snapshot_dir) $*.agda

snapshot_create_fot : $(snapshot_create_fot_files)
	@echo "$@ succeeded!"

snapshot_compare_fot : $(snapshot_compare_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# FOT: Prove theorems in the FOT

%.prove_fot :
	$(AGDA) -ifot $*.agda
	$(AGDA2ATP) -ifot --output-dir=$(output_dir) --time=240 $*.agda

prove_fot : $(prove_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# FOT: Consistency

%.consistency_fot :
	$(AGDA) -ifot $*.agda
	if ( $(AGDA2ATP) -ifot --output-dir=$(output_dir) \
	                 --time=10 $*.agda ); then \
           exit 1;\
        fi

consistency_fot : $(consistency_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# Notes: Type-checking

%.type_check_notes :
	$(AGDA) -ifot \
	        -inotes \
	        -inotes/agda-interface \
	        -inotes/fixed-points \
	        -inotes/issues \
                -inotes/papers/fossacs-2012 \
                -inotes/papers/paper-2011/ \
	        -inotes/README/ \
                -inotes/setoids/ \
                -inotes/thesis/logical-framework/ \
                -i $(std_lib_path)/src/ \
	        $*.agda

type_check_notes_aux : $(type_check_notes_files)

type_check_notes :
	cd $(std_lib_path) && darcs pull
	make type_check_notes_aux
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to Agda

agda_changed : clean
	if [ ! -d $(snapshot_dir) ]; then \
	   echo "Error: The directory $(snapshot_dir) does not exist"; \
	   exit 1; \
	fi
	cd agda2atp && cabal clean && cabal configure && cabal build
	make agda2atp_changed
	make type_check_fot
	make snapshot_compare_fot
	make type_check_notes
	cd utils/dump-agdai \
	&& cabal clean && cabal install
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to agda2atp

agda2atp_changed :
	@make generated_conjectures
	@make errors
	@make options
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a new ATP or a new version of an ATP

atp_changed :
	@make generated_conjectures
	@make prove_theorems
	@make refute_theorems
	@make errors
	@make options
	@make prove_fot
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to Coq.

%.coq_type_check :
	coqc $*.v

coq_changed : $(coq_type_check_files)
	@echo "$@ succeeded!"

##############################################################################
# Running the FOT and the notes

fot_and_notes :
	make type_check_fot
	make snapshot_create_fot
	type_check_notes
	@echo "$@ succeeded!"

##############################################################################
# Hlint test

hlint :
	hlint agda2atp/src/
	hlint utils/dump-agdai/src -i "Use on"
	hlint utils/fix-whitespace/
	@echo "$@ succeeded!"

##############################################################################
# Git : pre-commit test

git-pre-commit :
	@fix-whitespace --check
	@cd agda2atp && cabal configure && cabal build
	@make agda2atp_changed
	@make doc
	@make hlint
	@echo "$@ succeeded!"

##############################################################################
# Haskell program coverage

hpc_html_dir = agda2atp/hpc

hpc : hpc_clean
	cd agda2atp && cabal clean && cabal install --ghc-option=-fhpc
	make prove_theorems
	make refute_theorems
	make errors
	make options
	hpc markup --exclude=Paths_agda2atp \
	           --destdir=$(hpc_html_dir) \
	           --srcdir=agda2atp \
                   agda2atp.tix
	hpc report --exclude=Paths_agda2atp \
                   --decl-list \
	           --srcdir=agda2atp \
                   agda2atp.tix
	rm -f *.tix

hpc_clean :
	rm -f *.tix
	rm -f -r $(hpc_html_dir)

##############################################################################
# Benchmark

benchmark_tag = $(shell echo `date +"%Y%m%d-%H.%M"`-`hostname -s`)

%.benchmark :
	$(AGDA) -ifot $*.agda
	$(AGDA2ATP) -v 0 -ifot $*.agda \
                   +RTS -s/tmp/benchmark/$(subst /,.,$*)

benchmark_aux : $(benchmark_files)

.PHONY : benchmark
benchmark :
	mkdir --parents /tmp/benchmark
	make benchmark_aux
	mkdir --parents benchmark/$(benchmark_tag)
	mv /tmp/benchmark/* benchmark/$(benchmark_tag)/
	@echo "$@ succeeded!"

##############################################################################
# Others

dependency_graph :
	$(AGDA) -ifot \
	        --dependency-graph=/tmp/dependency-graph.gv \
	        fot/FOTC/Program/ABP/ProofSpecificationATP.agda
	dot -Tpdf /tmp/dependency-graph.gv > /tmp/dependency-graph.pdf

.PHONY : TAGS
TAGS : $(agda2atp_haskell_files)
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
