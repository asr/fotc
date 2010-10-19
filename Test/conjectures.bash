#! /bin/bash

# Test the conjecture files.

AGDA='agda -v 0'
# The time limit should be the maximum (--time=720) which is required
# by the postulate Examples.SortList.Closures.TreeOrdrightSubTree-TreeOrd.
AGDA2ATP='agda2atp --unproved-conjecture-error --time=180'

case $1 in
    LTC)
        files='
          LTC/Minimal/Properties
          LTC/Data/Bool/Properties
          LTC/Data/List/Properties
          LTC/Data/Nat/Divisibility/Properties
          LTC/Data/Nat/Inequalities/Properties
          LTC/Data/Nat/List/Properties
          LTC/Data/Nat/Properties
          LTC/Data/Nat/PropertiesByInduction
          LTC/Data/Stream/Bisimulation
          '
        ;;
    LTC-PCF)
        files='
          LTC-PCF/DataPCF/NatPCF/DivisibilityPCF/PropertiesPCF
          LTC-PCF/DataPCF/NatPCF/InequalitiesPCF/PropertiesPCF
          LTC-PCF/DataPCF/NatPCF/PropertiesPCF
          LTC-PCF/DataPCF/NatPCF/RecPCF/PropertiesPCF
          '
        ;;
    DivisionPCF)
        files='
          Examples/DivisionPCF/EquationsPCF
          Examples/DivisionPCF/IsN-PCF
          Examples/DivisionPCF/IsCorrectPCF
          '
        ;;
    GCD)
        files='
          Examples/GCD/IsN
          Examples/GCD/IsCommonDivisor
          Examples/GCD/IsDivisible
         '
        ;;
    GCD-PCF)
        files='
          Examples/GCD-PCF/EquationsPCF
          Examples/GCD-PCF/IsN-PCF
          Examples/GCD-PCF/IsCommonDivisorPCF
          Examples/GCD-PCF/IsDivisiblePCF
          '
        ;;
    Logic)
        files='
          Examples/Logic/Propositional
          Examples/Logic/Predicate
          '
        ;;
    SortList)
        files='
          Examples/SortList/Closures/Bool
          Examples/SortList/Closures/List
          Examples/SortList/Closures/ListOrd
          Examples/SortList/Closures/Tree
          Examples/SortList/Closures/TreeOrd
          Examples/SortList/ProofSpecification
          Examples/SortList/Properties
          '
        ;;
    Test)
        files='Test/LambdaLifting'
        ;;
    *) echo "Unrecognized value"
       exit
       ;;
esac

for file in ${files}; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} ${file}.agda ); then exit 1; fi
    if ! ( ${AGDA2ATP} ${file}.agda ); then exit 1; fi
done
