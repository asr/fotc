#! /bin/bash

AGDA='agda -v 0'

# TODO: Neither Equinox nor Eprove prove the theorems gcd-S>S and gcd-S≤S from
# Examples/GCD/EquationsPCF, therefore this file has not been added.

conjecturesFilesPCF='
  LTC/Data/NatPCF/DivisibilityPCF/PropertiesPCF
  LTC/Data/NatPCF/InequalitiesPCF/PropertiesPCF
  LTC/Data/NatPCF/PropertiesPCF
  LTC/Data/NatPCF/RecPCF/PropertiesPCF
  Examples/GCD-PCF/IsN-PCF
  Examples/GCD-PCF/IsCommonDivisorPCF
  Examples/GCD-PCF/IsDivisiblePCF
  '
for file in ${conjecturesFilesPCF} ; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} ${file}.agda ); then exit 1; fi
    if ! ( agda2atp --time 30 ${file}.agda ); then exit 1; fi
done
