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

# Notes path.
notes_path = notes

# Output directory for snapshot.
snapshot_dir = snapshot-fot

# Output directory for prove_fot.
prove_fot_dir = /tmp/prove_fot

# Output directory for consistency_fot.
consistency_fot_dir = /tmp/consistency_fot

# Output directory for prove_notes.
prove_notes_dir = /tmp/prove_notes

##############################################################################
# Variables

AGDA     = agda -v 0
AGDA_FOT = ${AGDA} -i$(fot_path)

# The defaults ATPs are E, Equinox and Vampire.
APIA = apia --check
# APIA = apia --atp=e
# APIA = apia --atp=equinox
# APIA = apia --atp=ileancop
# See notes/atps/README-summary-proofs.txt for using only metis
# APIA = apia --atp=metis
# APIA = apia --atp=spass
# APIA = apia --atp=vampire

APIA_FOT = ${APIA} -i$(fot_path)

##############################################################################
# Auxiliary functions

my_pathsubst = $(patsubst %.agda,%.$(1), \
	     	 $(shell find $(2) \( ! -path '*/Consistency/*' \) \
                              \( -name '*.agda' -and ! -name 'UnprovedATP.agda' \) \
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

create_snapshot_fot_files = $(call my_pathsubst,create_snapshot_fot,$(fot_path))

compare_snapshot_fot_files = \
  $(call my_pathsubst,compare_snapshot_fot,$(fot_path))

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
	$(AGDA_FOT) $*.agda

%.type_check_agsy_fot :
	$(AGDA_FOT) -i $(std_lib_path)/src/ $*.agda

type_check_fot : clean \
                 $(type_check_fot_files) \
                 $(type_check_agsy_fot_files)
	$(AGDA_FOT) $(fot_path)/README.agda
	@echo "$@ succeeded!"

##############################################################################
# FOT: Generated conjectures

# In FOT we use the create_snapshot_fot rule.

##############################################################################
# FOT: Snapshot

%.create_snapshot_fot :
	$(AGDA_FOT) $*.agda
	$(APIA_FOT) --only-files --output-dir=$(snapshot_dir) $*.agda

%.compare_snapshot_fot :
	@echo "Comparing $*.agda"
	@$(AGDA_FOT) $*.agda
	@$(APIA_FOT) -v 0 --snapshot-test \
	             --snapshot-dir=$(snapshot_dir) $*.agda

create_snapshot_fot_aux : $(create_snapshot_fot_files)

create_snapshot_fot :
	rm -r -f $(snapshot_dir)
	make create_snapshot_fot_aux
	@echo "$@ succeeded!"

compare_snapshot_fot : $(compare_snapshot_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# FOT: Prove theorems

%.prove_fot :
	$(AGDA_FOT) $*.agda
	$(APIA_FOT) --output-dir=$(prove_fot_dir) --time=240 $*.agda

prove_fot : $(prove_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# FOT: Consistency

%.consistency_fot :
	$(AGDA_FOT) $*.agda
	if ( $(APIA_FOT) --output-dir=$(consistency_fot_dir) \
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
  -i$(notes_path)/hip \
  -i$(notes_path)/k-axiom \
  -i$(notes_path)/papers/fossacs-2012 \
  -i$(notes_path)/papers/paper-2011/ \
  -i$(notes_path)/README \
  -i$(notes_path)/setoids \
  -i$(notes_path)/strictly-positive-inductive-types \
  -i$(notes_path)/thesis/report \
  -i$(notes_path)/type-classes

%.type_check_notes :
	$(AGDA) $(type_check_notes_path) $*.agda

type_check_notes : $(type_check_notes_files)
	@echo "$@ succeeded!"

##############################################################################
# Notes: Prove theorems

prove_notes_path = -i$(fot_path) \
                   -i$(notes_path) \
                    -i$(notes_path)/hip \
                   -i$(notes_path)/papers/fossacs-2012 \
                   -i$(notes_path)/thesis/report \
                   -i$(notes_path)/README

%.prove_notes :
	$(AGDA) $(prove_notes_path) $*.agda
	$(APIA) $(prove_notes_path) --output-dir=$(prove_notes_dir) \
	        --time=240 $*.agda

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
	make compare_snapshot_fot
	make type_check_notes
	make prove_notes
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to Apia

apia_changed :
	if [ ! -d $(snapshot_dir) ]; then \
	   echo "Error: The directory $(snapshot_dir) does not exist"; \
	   exit 1; \
	fi
	make prove_notes
	make compare_snapshot_fot
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a new ATP or a new version of an ATP

atp_changed :
	@make prove_notes
	@make prove_fot
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a new version of Coq.

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

##############################################################################
# Benchmark

benchmark_tag = \
  $(shell echo `date +"%Y%m%d-%H.%M"`-ghc-`ghc --numeric-version`-`hostname -s`)

%.benchmark :
	$(AGDA_FOT) $*.agda
	$(APIA_FOT) -v 0 $*.agda \
                +RTS -s/tmp/benchmark/$(subst /,.,$*)

benchmark_aux : $(benchmark_files)

.PHONY : benchmark
benchmark :
	mkdir --parents /tmp/benchmark
	make benchmark_aux
	mkdir --parents $(apia_path)/benchmark/$(benchmark_tag)
	mv /tmp/benchmark/* $(apia_path)/benchmark/$(benchmark_tag)/
	@echo "$@ succeeded!"

##############################################################################
# Hlint test

hlint :
	find -name '*.hs' | xargs hlint
	@echo "$@ succeeded!"

##############################################################################
# Others

dependency_graph :
	$(AGDA_FOT) --dependency-graph=/tmp/dependency-graph.gv \
	            $(fot_path)/FOTC/Program/ABP/ProofSpecificationATP.agda
	dot -Tpdf /tmp/dependency-graph.gv > /tmp/dependency-graph.pdf

peano_install :
	cd $(peano_path) && cabal install

TODO :
	find -wholename './dist' -prune -o -print \
	| xargs grep -I 'TODO' \
	| sort

clean :
	find -name '*.agdai' | xargs rm -f
	find -name '*.glob' | xargs rm -f
	find -name '*.hi' | xargs rm -f
	find -name '*.o' | xargs rm -f
	find -name '*.vo' | xargs rm -f
	find -name 'apia.tix' | xargs rm -f
	find -name 'model' | xargs rm -f
