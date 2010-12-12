#! /bin/bash

# Test the non-conjecture files.

non_conjectures_TPTP='/tmp/general-roles.tptp'

AGDA='agda -v 0'

files_with_non_conjectures='
  Examples/GCD/GCD
  LTC/Data/Nat
  LTC/Data/Nat/Inequalities
  LTC/Minimal
  '
for file in ${files_with_non_conjectures} ; do
    if ! ( ${AGDA} ${file}.agda ); then exit 1; fi
    if ! ( agda2atp --only-files ${file}.agda ); then exit 1; fi
    if ! ( cat ${file}.ax | while read -r line; do
                if ! ( grep --silent "${line}" ${non_conjectures_TPTP} ) ; then
                    echo "Testing error. Translation to: $line"
                    exit 1
                fi
            done
         ) ; then exit 1; fi
done
