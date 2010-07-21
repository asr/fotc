# Tunneling connection
host_dir = asicard@localhost:./tmp/Division/
port = 2024

AGDA = agda -v 0
local-path = Examples/DivisionPCF

conjecturesPCF :
	cd ../.. && ./test-conjectures.bash DivisionPCF

type-checking :
	cd ../.. && $(AGDA) $(local-path)/ProofSpecificationPCF.agda

type-checking-ER :
	cd ../.. && $(AGDA) $(local-path)/ProofSpecificationPCF-ER.agda

type-checking-all : type-checking-ER type-checking

test : type-checking-all conjecturesPCF

publish :
	rm -r -f html/

	cd ../../ && \
	$(AGDA) --html --html-dir=$(local-path)/html \
		$(local-path)/ProofSpecificationPCF.agda

	scp -P $(port) -r html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp

