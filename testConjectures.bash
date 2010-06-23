#! /bin/bash

AGDA='agda -v 0'

conjecturesFiles='
  LTC/Data/List/Properties
  LTC/Relation/Equalities/Properties
  LTC/Function/Arithmetic/Properties
  LTC/Relation/Inequalities/Properties
  LTC/Relation/Divisibility/Properties
  Examples/GCD/IsN
  Examples/GCD/IsCommonDivisor
  Examples/GCD/IsDivisible
  Test/Factorial
  '
for file in ${conjecturesFiles} ; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} ${file}.agda ); then exit 1; fi
    if ! ( agda2atp --time 60 ${file}.agda ); then exit 1; fi
done
