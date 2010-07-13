axioms :
	./Test/test-axioms.bash

conjectures :
	./Test/test-conjectures.bash

conjecturesPCF :
	./Test/test-conjecturesPCF.bash

only-type-checking :
	agda -v 0 Examples/GCD/IsGCD.agda
	agda -v 0 Examples/GCD/IsGCD-ER.agda
	agda -v 0 Examples/GCD-PCF/IsGCD-PCF.agda
	agda -v 0 Examples/GCD-PCF/IsGCD-PCF-ER.agda

test : only-type-checking axioms conjectures conjecturesPCF

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
