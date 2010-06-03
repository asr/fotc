testAxioms :
	./testAxioms.bash

testConjectures :
	./testConjectures.bash

testConjecturesPCF :
	./testConjecturesPCF.bash

testQuick :
	agda -v 0 Examples/GCD/IsGCD.agda
	agda -v 0 Examples/GCD/IsGCD-PCF.agda
	agda -v 0 Examples/GCD/IsGCD-ER.agda
	agda -v 0 Examples/GCD/IsGCD-PCF-ER.agda
	agda -v 0 LTC/Data/N/Induction/WellFounded.agda
	agda -v 0 LTC/Data/N/Induction/WellFoundedPCF.agda

test : testAxioms testConjectures testConjecturesPCF testQuick

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
