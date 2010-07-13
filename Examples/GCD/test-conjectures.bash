#! /bin/bash

AGDA='agda -v 0'
agda_path='/home/asr/code/phd/LTC/LTC-ATP/'

conjecturesFiles='
  IsN
  IsCommonDivisor
  IsDivisible
  '

for file in ${conjecturesFiles} ; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} -i ${agda_path} ${file}.agda ); then exit 1; fi
    if ! ( cd ${agda_path} &&
           agda2atp --time 40 Examples/GCD/${file}.agda ); then exit 1;
    fi
done
