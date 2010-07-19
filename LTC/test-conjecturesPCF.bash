#! /bin/bash

AGDA='agda -v 0'
local_path='LTC'

conjecturesFilesPCF='
  Data/NatPCF/DivisibilityPCF/PropertiesPCF
  Data/NatPCF/InequalitiesPCF/PropertiesPCF
  Data/NatPCF/PropertiesPCF
  Data/NatPCF/RecPCF/PropertiesPCF
  '

for file in ${conjecturesFilesPCF} ; do
    rm -f /tmp/*.tptp
    if ! ( cd ../ && ${AGDA} ${local_path}/${file}.agda ); then exit 1; fi
    if ! ( cd ../ && agda2atp --time 40 ${local_path}/${file}.agda )
       then exit 1
    fi
done
