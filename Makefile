testAxioms :
	./testAxioms.bash

testConjectures :
	./testConjectures.bash

testConjecturesPCF :
	./testConjecturesPCF.bash

testQuick :
	agda -v 0 Examples/GCD.agda
	agda -v 0 Examples/GCD-PCF.agda
	agda -v 0 Examples/GCD-ER.agda
	agda -v 0 Examples/GCD-PCF-ER.agda
	agda -v 0 LTC/Data/N/Induction/WellFounded.agda
	agda -v 0 LTC/Data/N/Induction/WellFoundedPCF.agda

test : testAxioms testConjectures testConjecturesPCF testQuick

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
