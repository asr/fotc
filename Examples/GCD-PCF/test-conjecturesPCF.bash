#! /bin/bash

AGDA='agda -v 0'
local_path='Examples/GCD-PCF'

# TODO: Neither Equinox nor Eprove prove the theorems gcd-S>S and gcd-S≤S from
# Examples/GCD/EquationsPCF, therefore this file has not been added.

conjecturesFilesPCF='
  IsN-PCF
  IsCommonDivisorPCF
  IsDivisiblePCF
  '

for file in ${conjecturesFilesPCF} ; do
    rm -f /tmp/*.tptp
    if ! ( cd ../.. && ${AGDA} ${local_path}/${file}.agda ); then exit 1; fi
    if ! ( cd ../.. && agda2atp --time 40 ${local_path}/${file}.agda )
       then exit 1
    fi
done
