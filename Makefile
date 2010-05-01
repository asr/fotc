testAxioms :
	./testAxioms.bash

testConjectures :
	./testConjectures.bash

testQuick :
	agda -v 0 Examples/GCD.agda
	agda -v 0 Examples/GCD-ER.agda

test : testAxioms testConjectures testQuick

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
	-rm -f /tmp/*.output
