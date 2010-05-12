testAxioms :
	./testAxioms.bash

testConjectures :
	./testConjectures.bash

testQuick :
	agda -v 0 Examples/GCD.agda
	agda -v 0 Examples/GCD-ER.agda
	agda -v 0 LTC/Data/N/Induction/WellFounded.agda

test : testAxioms testConjectures testQuick

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
