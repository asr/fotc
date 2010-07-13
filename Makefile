axioms :
	./Test/test-axioms.bash

conjectures :
	./Test/test-conjectures.bash

conjecturesPCF :

only-type-checking :

test : only-type-checking axioms conjectures conjecturesPCF

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
