testAxioms :
	./testAxioms.bash

testConjectures :
	./testConjectures.bash

testConjecturesPCF :
	./testConjecturesPCF.bash

testAgda :
	agda -v 0 Examples/DivisionPCF/IsDIV-PCF.agda
	agda -v 0 Examples/DivisionPCF/IsDIV-PCF-ER.agda
	agda -v 0 Examples/GCD/IsGCD.agda
	agda -v 0 Examples/GCD/IsGCD-ER.agda
	agda -v 0 Examples/GCD-PCF/IsGCD-PCF.agda
	agda -v 0 Examples/GCD-PCF/IsGCD-PCF-ER.agda
	agda -v 0 LTC/Data/Nat/Induction/WellFounded.agda

test : testAxioms testConjectures testConjecturesPCF testAgda

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
