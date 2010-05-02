#! /bin/bash

AGDA='agda -v 0'
axiomsFile='/tmp/axioms.tptp'

conjecturesFiles='
  Examples/GCD/IsCommonDivisor
  Examples/GCD/IsDivisible
  Examples/GCD/IsN
  LTC/Function/Arithmetic/Properties
  LTC/Relation/Divisibility/Properties
  LTC/Relation/Equalities/Properties
  LTC/Relation/Inequalities/Properties
  '
for file in ${conjecturesFiles} ; do
    rm -f /tmp/*.tptp /tmp/*.output
    if ! ( ${AGDA} ${file}.agda ); then exit 1; fi
    if ! ( agda2atp --time 60 ${file}.agda ); then exit 1; fi
done
