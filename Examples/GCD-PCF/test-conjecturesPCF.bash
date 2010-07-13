#! /bin/bash

AGDA='agda -v 0'
agda_path='/home/asr/code/phd/LTC/LTC-ATP/'

# TODO: Neither Equinox nor Eprove prove the theorems gcd-S>S and gcd-S≤S from
# Examples/GCD/EquationsPCF, therefore this file has not been added.

conjecturesFilesPCF='
  IsN-PCF
  IsCommonDivisorPCF
  IsDivisiblePCF
  '

for file in ${conjecturesFilesPCF} ; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} -i ${agda_path} ${file}.agda ); then exit 1; fi
    if ! ( cd ${agda_path} &&
           agda2atp --time 40 Examples/GCD-PCF/${file}.agda ); then exit 1;
    fi
done
