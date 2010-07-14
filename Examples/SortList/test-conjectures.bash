#! /bin/bash

AGDA='agda -v 0'
agda_path='/home/asr/code/phd/LTC/LTC-ATP/'

conjecturesFiles='
  Closures/Bool
  Closures/List
  Closures/ListOrd
  Closures/Tree
  Closures/TreeOrd
  ProofSpecification
  Properties
  '

for file in ${conjecturesFiles} ; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} -i ${agda_path} ${file}.agda ); then exit 1; fi
    if ! ( cd ${agda_path} &&
           agda2atp --time 120 Examples/SortList/${file}.agda ); then exit 1;
    fi
done
