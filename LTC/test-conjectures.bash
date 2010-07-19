#! /bin/bash

AGDA='agda -v 0'
local_path='LTC'

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
    if ! ( cd .. && ${AGDA} ${local_path}/${file}.agda ); then exit 1; fi
    if ! ( cd .. && agda2atp --time 40 ${local_path}/${file}.agda )
       then exit 1
    fi
done
