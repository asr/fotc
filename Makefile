non_conjectures :
	./test-non-conjectures.bash

conjectures :
	$(MAKE) -C LTC               conjectures
	$(MAKE) -C Examples/GCD      conjectures
	$(MAKE) -C Examples/Logic    conjectures
	$(MAKE) -C Examples/SortList conjectures

conjectures_PCF :
	$(MAKE) -C LTC-PCF              conjectures_PCF
	$(MAKE) -C Examples/DivisionPCF conjectures_PCF
	$(MAKE) -C Examples/GCD-PCF     conjectures_PCF

type_checking :
	$(MAKE) -C LTC                  type_checking
	$(MAKE) -C LTC-PCF              type_checking
	$(MAKE) -C Examples/DivisionPCF type_checking
	$(MAKE) -C Examples/GCD         type_checking
	$(MAKE) -C Examples/GCD-PCF     type_checking
	$(MAKE) -C Examples/Logic       type_checking
	$(MAKE) -C Examples/SortList    type_checking

type_checking_ER :
	$(MAKE) -C LTC                  type_checking_ER
	$(MAKE) -C LTC-PCF              type_checking_ER
	$(MAKE) -C Examples/DivisionPCF type_checking_ER
	$(MAKE) -C Examples/GCD         type_checking_ER
	$(MAKE) -C Examples/GCD-PCF     type_checking_ER
	$(MAKE) -C Examples/SortList    type_checking_ER

type_checking_all : type_checking_ER type_checking

test : type_checking_all non_conjectures conjectures conjectures_PCF

publish :
	$(MAKE) -C LTC                  publish
	$(MAKE) -C LTC-PCF              publish
	$(MAKE) -C Examples/DivisionPCF publish
	$(MAKE) -C Examples/GCD         publish
	$(MAKE) -C Examples/GCD-PCF     publish
	$(MAKE) -C Examples/Logic       publish
	$(MAKE) -C Examples/SortList    publish

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
