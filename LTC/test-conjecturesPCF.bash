#! /bin/bash

AGDA='agda -v 0'
agda_path='/home/asr/code/phd/LTC/LTC-ATP/'

conjecturesFilesPCF='
  Data/NatPCF/DivisibilityPCF/PropertiesPCF
  Data/NatPCF/InequalitiesPCF/PropertiesPCF
  Data/NatPCF/PropertiesPCF
  Data/NatPCF/RecPCF/PropertiesPCF
  '

for file in ${conjecturesFilesPCF} ; do
    rm -f /tmp/*.tptp
    if ! ( ${AGDA} -i ${agda_path} ${file}.agda ); then exit 1; fi
    if ! ( cd ${agda_path} &&
           agda2atp --time 40 LTC/${file}.agda ); then exit 1;
    fi
done
