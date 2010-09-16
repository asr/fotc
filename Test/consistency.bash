#! /bin/bash

# Test the consistency files.

AGDA='agda -v 0'
AGDA2ATP='agda2atp --atp=equinox --atp=eprover --time=10 '
AGDA2ATP="$AGDA2ATP"--unproved-conjecture-error

case $1 in
    LTC)
        files='
          Test/Consistency/LTC/Minimal
          Test/Consistency/LTC/Data/Bool
          Test/Consistency/LTC/Data/List
          Test/Consistency/LTC/Data/List/Bisimulation
          Test/Consistency/LTC/Data/Nat
          Test/Consistency/LTC/Data/Nat/Inequalities
          '
        ;;
    GCD)
        files='
          Test/Consistency/Examples/GCD/GCD
         '
        ;;
    SortList)
        files='
          Test/Consistency/Examples/SortList/SortList
          '
        ;;
    *) echo "Unrecognized value"
       exit
       ;;
esac

for file in ${files}; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} ${file}.agda ); then exit 1; fi
# Because we are using the option --unproved-conjecture-error we
# revert the Agda output.
    if ( ${AGDA2ATP} ${file}.agda ); then exit 1; fi
done
