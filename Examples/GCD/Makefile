# Tunneling connection
host_dir = asicard@localhost:./tmp/GCD/
port = 2024

AGDA = agda -v 0
local-path = Examples/GCD

conjectures :
	./test-conjectures.bash

type-checking :
	cd ../.. && $(AGDA) $(local-path)/ProofSpecification.agda

type-checking-ER :
	cd ../.. && $(AGDA) $(local-path)/ProofSpecificationER.agda

type-checking-all : type-checking-ER type-checking

test : type-checking-all conjectures

publish :
	rm -r -f html/

	cd ../.. && \
	$(AGDA) --html --html-dir=$(local-path)/html \
		$(local-path)/ProofSpecification.agda

	scp -P $(port) -r html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
