#! /bin/bash

AGDA='agda -v 0'
local_path='Examples/DivisionPCF'

conjecturesFilesPCF='
  EquationsPCF
  IsN-PCF
  IsCorrectPCF
  '

for file in ${conjecturesFilesPCF} ; do
    rm -f /tmp/*.tptp
    if ! ( cd ../.. && ${AGDA} ${local_path}/${file}.agda ); then exit 1; fi
    if ! ( cd ../.. && agda2atp --time 40 ${local_path}/${file}.agda )
       then exit 1
    fi
done
