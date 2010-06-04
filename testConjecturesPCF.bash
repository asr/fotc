#! /bin/bash

AGDA='agda -v 0'

conjecturesFilesPCF='
  LTC/Function/Rec/Properties
  LTC/Function/Arithmetic/PropertiesPCF
  LTC/Relation/Inequalities/PropertiesPCF
  LTC/Relation/Divisibility/PropertiesPCF
  Examples/GCD/IsN-PCF
  Examples/GCD/IsCommonDivisorPCF
  Examples/GCD/IsDivisiblePCF
  Examples/Division/Equations
  Examples/Division/IsN
  Examples/Division/IsCorrect
  '
for file in ${conjecturesFilesPCF} ; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} ${file}.agda ); then exit 1; fi
    if ! ( agda2atp --time 30 ${file}.agda ); then exit 1; fi
done
