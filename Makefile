axioms :
	./test-axioms.bash

conjectures :
	$(MAKE) -C LTC               conjectures
	$(MAKE) -C Examples/GCD      conjectures
	$(MAKE) -C Examples/SortList conjectures

conjecturesPCF :
	$(MAKE) -C LTC                  conjecturesPCF
	$(MAKE) -C Examples/DivisionPCF conjecturesPCF
	$(MAKE) -C Examples/GCD-PCF     conjecturesPCF

only-type-checking :
	$(MAKE) -C LTC                  only-type-checking
	$(MAKE) -C Examples/DivisionPCF only-type-checking
	$(MAKE) -C Examples/GCD         only-type-checking
	$(MAKE) -C Examples/GCD-PCF     only-type-checking
	$(MAKE) -C Examples/SortList    only-type-checking

publish :
	$(MAKE) -C LTC                  publish
	$(MAKE) -C Examples/DivisionPCF publish
	$(MAKE) -C Examples/GCD         publish
	$(MAKE) -C Examples/GCD-PCF     publish
	$(MAKE) -C Examples/SortList    publish

test : only-type-checking axioms conjectures conjecturesPCF

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
