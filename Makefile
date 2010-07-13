axioms :
	./Test/test-axioms.bash

conjectures :
	./Test/test-conjectures.bash

conjecturesPCF :
	./Test/test-conjecturesPCF.bash

only-type-checking :
	agda -v 0 Examples/DivisionPCF/IsDIV-PCF.agda
	agda -v 0 Examples/DivisionPCF/IsDIV-PCF-ER.agda
	agda -v 0 Examples/GCD/IsGCD.agda
	agda -v 0 Examples/GCD/IsGCD-ER.agda
	agda -v 0 Examples/GCD-PCF/IsGCD-PCF.agda
	agda -v 0 Examples/GCD-PCF/IsGCD-PCF-ER.agda
	agda -v 0 LTC/Data/Nat/Induction/WellFounded.agda
	agda -v 0 LTC/Minimal/PropertiesER.agda

test : only-type-checking axioms conjectures conjecturesPCF

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
