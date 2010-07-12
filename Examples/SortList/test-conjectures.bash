#! /bin/bash

AGDA='agda -v 0'

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
    if ! ( ${AGDA} -i /home/asr/code/phd/LTC/LTC-ATP/ ${file}.agda ); then exit 1; fi
    if ! ( cd /home/asr/code/phd/LTC/LTC-ATP && agda2atp --time 40 Examples/SortList/${file}.agda ); then exit 1; fi
done
