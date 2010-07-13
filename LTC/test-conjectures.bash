#! /bin/bash

AGDA='agda -v 0'
agda_path='/home/asr/code/phd/LTC/LTC-ATP/'

conjecturesFiles='
  Minimal/Properties
  Data/Bool/Properties
  Data/List/Properties
  Data/Nat/Divisibility/Properties
  Data/Nat/Inequalities/Properties
  Data/Nat/List/Properties
  Data/Nat/Properties
  Relation/Equalities/Properties
  '

for file in ${conjecturesFiles} ; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} -i ${agda_path} ${file}.agda ); then exit 1; fi
    if ! ( cd ${agda_path} &&
           agda2atp --time 40 LTC/${file}.agda ); then exit 1;
    fi
done
