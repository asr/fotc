#! /bin/bash

AGDA='agda -v 0'

conjecturesFilesRec='
  LTC/Function/Rec/Properties
  LTC/Function/Arithmetic/PropertiesRec
  LTC/Relation/Inequalities/PropertiesRec
  LTC/Relation/Divisibility/PropertiesRec
  Examples/GCD/IsN-Rec
  Examples/GCD/IsCommonDivisorRec
  Examples/GCD/IsDivisibleRec
  '
for file in ${conjecturesFilesRec} ; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} ${file}.agda ); then exit 1; fi
    if ! ( agda2atp --time 30 ${file}.agda ); then exit 1; fi
done
