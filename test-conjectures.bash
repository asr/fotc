#! /bin/bash

# Test the conjecture files.

AGDA='agda -v 0'
AGDA2ATP='agda2atp --time 40'

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
          LTC/Relation/Equalities/Properties
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
# TODO: Neither Equinox nor Eprove prove the theorems gcd-S>S and gcd-S≤S from
# Examples/GCD-PCF/EquationsPCF, therefore this file has not been added.
    GCD-PCF)
        files='
          Examples/GCD-PCF/IsN-PCF
          Examples/GCD-PCF/IsCommonDivisorPCF
          Examples/GCD-PCF/IsDivisiblePCF
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
    *) echo "Unrecognized value"
       exit
       ;;
esac

for file in ${files} ; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} ${file}.agda ); then exit 1; fi
    if ! ( ${AGDA2ATP} ${file}.agda ); then exit 1; fi
done
