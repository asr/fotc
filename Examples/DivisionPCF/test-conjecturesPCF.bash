#! /bin/bash

AGDA='agda -v 0'

conjecturesFilesPCF='
  EquationsPCF
  IsN-PCF
  IsCorrectPCF
  '

for file in ${conjecturesFilesPCF} ; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} -i /home/asr/code/phd/LTC/LTC-ATP/ ${file}.agda ); then exit 1; fi
    if ! ( cd /home/asr/code/phd/LTC/LTC-ATP && agda2atp --time 40 Examples/DivisionPCF/${file}.agda ); then exit 1; fi
done
