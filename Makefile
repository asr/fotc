testAxioms :
	./testAxioms.bash

testConjectures :
	./testConjectures.bash

testConjecturesPCF :
	./testConjecturesPCF.bash

testAgda :
	agda -v 0 Examples/GCD/IsGCD.agda
	agda -v 0 Examples/GCD/IsGCD-PCF.agda
	agda -v 0 Examples/GCD/IsGCD-ER.agda
	agda -v 0 Examples/GCD/IsGCD-PCF-ER.agda
	agda -v 0 Examples/Division/IsDIV-PCF.agda
	agda -v 0 Examples/Division/IsDIV-PCF-ER.agda
	agda -v 0 LTC/Data/N/Induction/WellFounded.agda

test : testAxioms testConjectures testConjecturesPCF testAgda

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
