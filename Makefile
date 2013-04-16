# Tested with:
# GNU Make 3.81 and
# GNU bash, version 4.2.8(1)-release (x86_64-pc-linux-gnu)

SHELL := /bin/bash

##############################################################################
# Paths

fot_path   = src/fot
peano_path = src/peano

# Agda standard library path.
std_lib_path = ~/agda-upstream/std-lib

# Directory for the TPTP files.
output_dir = /tmp/fotc

# Notes path.
notes_path = notes

# Snapshot fot directory.
snapshot_dir = snapshot-fot

##############################################################################
# Variables

AGDA = agda -v 0

# The defaults ATPs are e, equinox, and vampire.
AGDA2ATP = agda2atp
# AGDA2ATP = agda2atp --atp=e
# AGDA2ATP = agda2atp --atp=equinox
# AGDA2ATP = agda2atp --atp=ileancop
# See notes/atps/README-summary-proofs.txt for using only metis
# AGDA2ATP = agda2atp --atp=metis
# AGDA2ATP = agda2atp --atp=spass
# AGDA2ATP = agda2atp --atp=vampire

##############################################################################
# Auxiliary functions

my_pathsubst = $(patsubst %.agda,%.$(1), \
	     	 $(shell find $(2) \( ! -path '*/Consistency/*' \) -name '*.agda' \
		 	 | xargs grep -L 'The ATPs could not prove the theorem' \
			 | xargs grep -l 'ATP prove' \
		  	 | sort))

##############################################################################
# Files

# FOT

type_check_fot_files = \
  $(patsubst %.agda,%.type_check_fot, \
    $(shell find $(fot_path) -name 'Everything.agda' | sort))

type_check_agsy_fot_files = \
  $(patsubst %.agda,%.type_check_agsy_fot, \
    $(shell find $(fot_path)/Agsy/ -name '*.agda' | sort))

snapshot_create_fot_files = $(call my_pathsubst,snapshot_create_fot,$(fot_path))

snapshot_compare_fot_files = \
  $(call my_pathsubst,snapshot_compare_fot,$(fot_path))

prove_fot_files = $(call my_pathsubst,prove_fot,$(fot_path))

consistency_fot_files = \
  $(patsubst %.agda,%.consistency_fot, \
    $(shell find $(fot_path) -path '*/Consistency/*' -name '*.agda' | sort))

# Notes

type_check_notes_files = \
  $(patsubst %.agda,%.type_check_notes, \
    $(shell find $(notes_path) -name '*.agda' | sort))

prove_notes_files = $(call my_pathsubst,prove_notes,$(notes_path))

# Others

coq_type_check_files = $(patsubst %.v,%.coq_type_check, \
	               $(shell find -name '*.v' | sort))

benchmark_files = \
  $(fot_path)/FOTC/Base/PropertiesATP.benchmark \
  $(fot_path)/FOTC/Program/GCD/Partial/ProofSpecificationATP.benchmark \
  $(fot_path)/FOTC/Program/SortList/ProofSpecificationATP.benchmark

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

type_check_notes_path = \
  -i$(fot_path) \
  -i $(std_lib_path)/src/ \
  -i$(notes_path) \
  -i$(notes_path)/discrimination-rules \
  -i$(notes_path)/fixed-points \
  -i$(notes_path)/k-rule	 \
  -i$(notes_path)/papers/fossacs-2012 \
  -i$(notes_path)/papers/paper-2011/ \
  -i$(notes_path)/README \
  -i$(notes_path)/setoids \
  -i$(notes_path)/strictly-positive-inductive-types \
  -i$(notes_path)/thesis \
  -i$(notes_path)/type-classes

%.type_check_notes :
	$(AGDA) $(type_check_notes_path) $*.agda

type_check_notes : $(type_check_notes_files)
	@echo "$@ succeeded!"

##############################################################################
# Notes: Prove theorems

prove_notes_path = -i$(fot_path) \
                   -i$(notes_path) \
                   -i$(notes_path)/papers/fossacs-2012 \
                   -i$(notes_path)/thesis/ \
                   -i$(notes_path)/README

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
	cd $(std_lib_path) && darcs pull
	make type_check_fot
	make snapshot_compare_fot
	make type_check_notes
	make prove_notes
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to Agda

agda2atp_changed :
	if [ ! -d $(snapshot_dir) ]; then \
	   echo "Error: The directory $(snapshot_dir) does not exist"; \
	   exit 1; \
	fi
	make prove_notes
	make snapshot_compare_fot
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a new ATP or a new version of an ATP

atp_changed :
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

fot_changed :
	make type_check_fot
	make type_check_notes
	@echo "$@ succeeded!"

##############################################################################
# Git : pre-commit test

git_pre_commit :
	fix-whitespace --check
	@echo "$@ succeeded!"

install :
	cd $(peano_path) && cabal install

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

ToDo :
	find -wholename './dist' -prune -o -print \
	| xargs grep -I 'ToDo:' \
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
