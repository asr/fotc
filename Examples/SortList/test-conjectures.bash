#! /bin/bash

AGDA='agda -v 0'
local_path='Examples/SortList'

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
    if ! ( cd ../.. && ${AGDA} ${local_path}/${file}.agda ); then exit 1; fi
    if ! ( cd ../../ && agda2atp --time 120 ${local_path}/${file}.agda )
       then exit 1
    fi
done
