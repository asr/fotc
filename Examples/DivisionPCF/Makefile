# Tunneling connection
host_dir = asicard@localhost:./tmp/Division/
port = 2024

AGDA = agda -v 0
local_path = Examples/DivisionPCF

conjectures_PCF :
	cd ../.. && ./test-conjectures.bash DivisionPCF

type_checking :
	cd ../.. && $(AGDA) $(local_path)/ProofSpecificationPCF.agda

type_checking_ER :
	cd ../.. && $(AGDA) $(local_path)/ProofSpecificationPCF-ER.agda

type_checking_all : type_checking_ER type_checking

test : type_checking_all conjectures_PCF

publish :
	rm -r -f html/

	cd ../../ && \
	$(AGDA) --html --html-dir=$(local_path)/html \
		$(local_path)/ProofSpecificationPCF.agda

	scp -P $(port) -r html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp

