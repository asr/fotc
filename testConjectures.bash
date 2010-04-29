#! /bin/bash

# ATP='equinox-2.0'
ATP='equinox-cvs'
AGDA='agda -v 0'
axiomsFile='/tmp/axioms.tptp'

conjecturesFiles='
  Examples/GCD/Properties/IsCommonDivisor
  Examples/GCD/Properties/IsDivisible
  Examples/GCD/Properties/IsN
  LTC/Function/Arithmetic/Properties
  LTC/Relation/Divisibility/Properties
  LTC/Relation/Equalities/Properties
  LTC/Relation/Inequalities/Properties
  '
for file in ${conjecturesFiles} ; do
    rm -f /tmp/*.tptp /tmp/*.output
    if ! ( ${AGDA} ${file}.agda ); then exit 1; fi
    if ! ( agda2atp ${file}.agda ); then exit 1; fi
    for fileTPTP in /tmp/*.tptp; do
        if [ "${fileTPTP}" != ${axiomsFile} ]; then
            echo "Proving ${fileTPTP} ..."
            ${ATP} ${fileTPTP} > ${fileTPTP}.output
            if ! ( grep --silent "+++ RESULT: Theorem" ${fileTPTP}.output )
            then
                echo "Testing error in file ${fileTPTP}"
                exit 1
            fi
        fi
    done
done
