SHELL := /bin/bash

##############################################################################
# Paths

fot_path = src/fot

# Notes path.
notes_path = notes

# Output directory for snapshot.
snapshot_dir = snapshot-fot

# Output directory for prove-fot.
prove_fot_dir = /tmp/prove-fot

# Output directory for consistency-fot.
consistency_fot_dir = /tmp/consistency-fot

# Output directory for prove-notes.
prove_notes_dir = /tmp/prove-notes

##############################################################################
# Variables

AGDA = agda -v 0

APIA = apia --check --atp=e --atp=equinox --atp=vampire
# APIA = apia --atp=e
# APIA = apia --atp=equinox
# APIA = apia --atp=ileancop
# APIA = apia --atp=metis
# APIA = apia --atp=spass
# APIA = apia --atp=vampire

APIA_FOT = ${APIA} -i$(fot_path)

##############################################################################
# Auxiliary functions

my_pathsubst = \
  $(patsubst %.agda, %.$(1), \
    $(shell find $(2) \( ! -path '*/Consistency/*' \) \
                      \( -name '*.agda' -and ! -name 'UnprovedATP.agda' \) \
            | xargs grep -l 'ATP prove' \
            | sort))

##############################################################################
# Files

# FOT

type_check_fot_files = \
  $(patsubst %.agda, %.type-check-fot, \
    $(shell find $(fot_path) -name 'Everything.agda' | sort))

type_check_agsy_fot_files = \
  $(patsubst %.agda, %.type-check-agsy-fot, \
    $(shell find $(fot_path)/Agsy/ -name '*.agda' | sort))

create_snapshot_fot_files = \
  $(call my_pathsubst,create-snapshot-fot,$(fot_path))

compare_snapshot_fot_files = \
  $(call my_pathsubst,compare-snapshot-fot,$(fot_path))

only_fot_files = $(call my_pathsubst,only-fot,$(fot_path))

prove_fot_files = $(call my_pathsubst,prove-fot,$(fot_path))

consistency_fot_files = \
  $(patsubst %.agda, %.consistency-fot, \
    $(shell find $(fot_path) -path '*/Consistency/*' -name '*.agda' | sort))

# Notes

type_check_agsy_notes_files = \
  $(patsubst %.agda, %.type-check-agsy-notes, \
    $(shell find $(notes_path)/FOT/Agsy/ -name '*.agda' | sort))

type_check_notes_files = \
  $(patsubst %.agda, %.type-check-notes, \
    $(shell find $(notes_path) -name '*.agda' | sort))

stdlib_changed_files = \
  $(patsubst %.agda, %.stdlib-changed, \
    $(shell find $(notes_path) -name '*SL.agda' | sort))

prove_notes_files = $(call my_pathsubst,prove-notes,$(notes_path))

# Others

coq_type_check_files = \
  $(patsubst %.v, %.coq-type-check, \
    $(shell find -name '*.v' | sort))

ghc_files = \
  $(patsubst %.hs, %.ghc, \
    $(shell find -name '*.hs' | sort))

peano_files = \
  $(patsubst %.hs, %.peano, \
    $(shell find -name '*.hs' | xargs grep -l 'import Data.\Peano' | sort))

benchmark_files = \
  $(fot_path)/FOTC/Base/PropertiesATP.benchmark \
  $(fot_path)/FOTC/Program/GCD/Partial/ProofSpecificationATP.benchmark \
  $(fot_path)/FOTC/Program/SortList/ProofSpecificationATP.benchmark

##############################################################################
# FOT: Type-checking

%.type-check-fot :
	$(AGDA) $*.agda

%.type-check-agsy-fot :
	$(AGDA) $*.agda

type-check-agsy-fot : $(type_check_agsy_fot_files)
	@echo "$@ succeeded!"

type-check-fot : $(type_check_fot_files)
	make type-check-agsy-fot
	$(AGDA) $(fot_path)/README.agda
	@echo "$@ succeeded!"

##############################################################################
# FOT: Generated conjectures

# In FOT we use the create-snapshot-fot rule.

##############################################################################
# FOT: Snapshot

%.create-snapshot-fot :
	$(AGDA) $*.agda
	@case $*.agda in \
          "${fot_path}/FOL/NonIntuitionistic/TheoremsATP.agda" | \
          "${fot_path}/FOL/SchemataATP.agda") \
            $(APIA_FOT) --only-files \
                        --output-dir=$(snapshot_dir) \
                        --schematic-propositional-functions \
                        --schematic-propositional-symbols  \
                        $*.agda \
          ;; \
          *) \
            $(APIA_FOT) --only-files --output-dir=$(snapshot_dir) $*.agda \
            ;; \
        esac

%.compare-snapshot-fot :
	@echo "Comparing $*.agda..."
	@$(AGDA) $*.agda
	@case $*.agda in \
          "${fot_path}/FOL/NonIntuitionistic/TheoremsATP.agda" | \
          "${fot_path}/FOL/SchemataATP.agda") \
            $(APIA_FOT) -v 0 \
                        --snapshot-test \
	                --snapshot-dir=$(snapshot_dir) \
                        --schematic-propositional-functions \
                        --schematic-propositional-symbols  \
                        $*.agda \
          ;; \
          *) \
            $(APIA_FOT) -v 0 \
                        --snapshot-test \
	                --snapshot-dir=$(snapshot_dir) \
                        $*.agda \
            ;; \
        esac

create-snapshot-fot-aux : $(create_snapshot_fot_files)

create-snapshot-fot :
	rm -r -f $(snapshot_dir)
	make create-snapshot-fot-aux
	@echo "$@ succeeded!"

compare-snapshot-fot : $(compare_snapshot_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# FOT: Only files

%.only-fot :
	$(AGDA) $*.agda
	case $*.agda in \
          "${fot_path}/FOL/NonIntuitionistic/TheoremsATP.agda" | \
          "${fot_path}/FOL/SchemataATP.agda") \
            $(APIA_FOT) --only-files \
                        --output-dir=$(prove_fot_dir) \
                        --schematic-propositional-functions \
                        --schematic-propositional-symbols  \
                        $*.agda \
          ;; \
          *) \
	    $(APIA_FOT) --only-files --output-dir=$(prove_fot_dir) $*.agda \
            ;; \
        esac

only-fot : $(only_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# FOT: Prove theorems

%.prove-fot :
	$(AGDA) $*.agda
	case $*.agda in \
          "${fot_path}/FOL/NonIntuitionistic/TheoremsATP.agda" | \
          "${fot_path}/FOL/SchemataATP.agda") \
            $(APIA_FOT) --output-dir=$(prove_fot_dir) \
	                --time=300 \
                        --schematic-propositional-functions \
                        --schematic-propositional-symbols  \
                        $*.agda \
          ;; \
          *) \
            $(APIA_FOT) --output-dir=$(prove_fot_dir) --time=300 $*.agda \
            ;; \
        esac

prove-fot : $(prove_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# FOT: Consistency

%.consistency-fot :
	$(AGDA) $*.agda
	if ( $(APIA_FOT) --output-dir=$(consistency_fot_dir) \
	                 --time=10 $*.agda ); then \
           exit 1;\
        fi

consistency-fot : $(consistency_fot_files)
	@echo "$@ succeeded!"

##############################################################################
# Notes: Type-checking

%.type-check-agsy-notes :
	$(AGDA) $*.agda

# Only used for testing changes in the standard library.
type-check-agsy-notes : $(type_check_agsy_notes_files)
	@echo "$@ succeeded!"

%.type-check-notes :
	$(AGDA) $*.agda

type-check-notes : $(type_check_notes_files)
	@echo "$@ succeeded!"

##############################################################################
# Notes: Prove theorems

prove_notes_path = -i$(notes_path)/hip \
                   -i$(notes_path)/papers/fossacs-2012 \
                   -i$(notes_path)/thesis/report \
                   -i$(notes_path)/README

%.prove-notes :
	$(AGDA) $(prove_notes_path) $*.agda
	case $*.agda in \
          "${notes_path}/FOT/FOL/MendelsonSubstATP.agda" | \
          "${notes_path}/FOT/FOL/SchemataATP.agda" | \
          "${notes_path}/FOT/FOL/SchemataInstances/TestATP.agda" | \
          "${notes_path}/FOT/FOTC/Data/Bool/AndTotality.agda" | \
          "${notes_path}/thesis/report/CombiningProofs/ForallExistSchema.agda") \
            $(APIA_FOT) $(prove_notes_path) \
                        --output-dir=$(prove_notes_dir) \
	                --time=300 \
                        --schematic-propositional-functions \
                        $*.agda \
          ;; \
          "${notes_path}/papers/fossacs-2012/Examples.agda" | \
          "${notes_path}/thesis/report/CombiningProofs/CommDisjunctionSchema.agda") \
            $(APIA_FOT) $(prove_notes_path) \
                        --output-dir=$(prove_notes_dir) \
	                --time=300 \
                        --schematic-propositional-symbols \
                        $*.agda \
          ;; \
          *) \
            $(APIA) $(prove_notes_path) \
                    --output-dir=$(prove_notes_dir) \
	            --time=300 \
                    $*.agda \
            ;; \
        esac

prove-notes : $(prove_notes_files)
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to Agda

agda-changed : clean
	if [ ! -d $(snapshot_dir) ]; then \
	   echo "Error: The directory $(snapshot_dir) does not exist"; \
	   exit 1; \
	fi
	make type-check-fot
	make compare-snapshot-fot
	make type-check-notes
	make prove-notes
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to the Agda standard library

%.stdlib-changed :
	$(AGDA) $*.agda

stdlib-changed-aux : $(stdlib_changed_files)

stdlib-changed :
	make type-check-agsy-fot
	make type-check-agsy-notes
	make stdlib-changed-aux
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to Apia

apia-changed :
	if [ ! -d $(snapshot_dir) ]; then \
	   echo "Error: The directory $(snapshot_dir) does not exist"; \
	   exit 1; \
	fi
	make compare-snapshot-fot
	make prove-notes
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a new ATP or a new version of an ATP

atp-changed :
	@make prove-notes
	@make prove-fot
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a new version of Coq.

%.coq-type-check :
	coqc -w all $*.v

coq-changed : coq-clean $(coq_type_check_files)
	@echo "$@ succeeded!"

coq-clean :
	rm -f *.glob *.vo

##############################################################################
# Test used when there is a modification to FOT.

fot-changed :
	make type-check-fot
	make type-check-notes
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a new version of GHC.

%.ghc :
	@rm -f $*.hi
	@rm -f $*.o
	ghc -Wall -Werror $*.hs

ghc-changed : $(ghc_files)
	@echo "$@ succeeded!"

##############################################################################
# Test used when there is a modification to the Peano library.

%.peano :
	@rm -f $*.hi
	@rm -f $*.o
	ghc -Wall -Werror $*.hs

peano-changed : $(peano_files)
	@echo "$@ succeeded!"

##############################################################################
# Git : pre-commit test

git-pre-commit :
	fix-whitespace --check
	make type-check-fot
	make type-check-notes
	@echo "$@ succeeded!"

##############################################################################
# Benchmark

benchmark_tag = \
  $(shell echo `date +"%Y%m%d-%H.%M"`-ghc-`ghc --numeric-version`-`hostname -s`)

# TODO (19 June 2015): Pragmas/options were removed/added from/to
# Agda/Apia.

%.benchmark :
	$(AGDA_FOT) $*.agda
	$(APIA_FOT) -v 0 $*.agda \
                +RTS -s/tmp/benchmark/$(subst /,.,$*)

benchmark-aux : $(benchmark_files)

.PHONY : benchmark
benchmark :
	mkdir --parents /tmp/benchmark
	make benchmark-aux
	mkdir --parents $(apia_path)/benchmark/$(benchmark_tag)
	mv /tmp/benchmark/* $(apia_path)/benchmark/$(benchmark_tag)/
	@echo "$@ succeeded!"

##############################################################################
# Hlint test

hlint :
	find -name '*.hs' | xargs hlint --color=never
	@echo "$@ succeeded!"

##############################################################################
# ATP stuff

add-ATP-stuff :
	src/utils/sed/add-ATP-stuff.bash

remove-ATP-stuff :
	src/utils/sed/remove-ATP-stuff.bash

##############################################################################
# Others

dependency-graph :
	$(AGDA_FOT) --dependency-graph=/tmp/dependency-graph.gv \
	            $(fot_path)/FOTC/Program/ABP/ProofSpecificationATP.agda
	dot -Tpdf /tmp/dependency-graph.gv > /tmp/dependency-graph.pdf

TODO :
	find . -type d \( -path './.git' -o -path './dist' \) -prune -o -print \
	| xargs grep -I 'TODO' \
	| sort

clean :
	find . -type f -name '*.agdai' -delete
	find . -type f -name '*.glob' -delete
	find . -type f -name '*.hi' -delete
	find . -type f -name '*.o' -delete
	find . -type f -name '*.vo' -delete
	find . -type f -name 'apia.tix' -delete
	find . -type f -name 'model' -delete
