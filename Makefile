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

type-checking :
	$(MAKE) -C LTC                  type-checking
	$(MAKE) -C Examples/DivisionPCF type-checking
	$(MAKE) -C Examples/GCD         type-checking
	$(MAKE) -C Examples/GCD-PCF     type-checking
	$(MAKE) -C Examples/SortList    type-checking

type-checking-ER :
	$(MAKE) -C LTC                  type-checking-ER
	$(MAKE) -C Examples/DivisionPCF type-checking-ER
	$(MAKE) -C Examples/GCD         type-checking-ER
	$(MAKE) -C Examples/GCD-PCF     type-checking-ER
	$(MAKE) -C Examples/SortList    type-checking-ER

type-checking-all : type-checking-ER type-checking

test : type-checking-all axioms conjectures conjecturesPCF

publish :
	$(MAKE) -C LTC                  publish
	$(MAKE) -C Examples/DivisionPCF publish
	$(MAKE) -C Examples/GCD         publish
	$(MAKE) -C Examples/GCD-PCF     publish
	$(MAKE) -C Examples/SortList    publish

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
