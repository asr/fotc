testAxioms :
	./testAxioms.bash

testConjectures :
	./testConjectures.bash

testConjecturesRec :
	./testConjecturesRec.bash

testQuick :
	agda -v 0 Examples/GCD.agda
	agda -v 0 Examples/GCD-Rec.agda
	agda -v 0 Examples/GCD-ER.agda
	agda -v 0 Examples/GCD-RecER.agda
	agda -v 0 LTC/Data/N/Induction/WellFounded.agda
	agda -v 0 LTC/Data/N/Induction/WellFoundedRec.agda

test : testAxioms testConjectures testConjecturesRec testQuick

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
