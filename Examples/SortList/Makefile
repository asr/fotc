# Tunneling connection
host_dir = asicard@localhost:./tmp/SortList/
port = 2024

AGDA = agda -v 0
agda-path = /home/asr/code/phd/LTC/LTC-ATP/

conjectures :
	./test-conjectures.bash

type-checking :
	$(AGDA) -i $(agda-path) ProofSpecification.agda

type-checking-ER :
	$(AGDA) -i $(agda-path) Closures/ListER.agda
	$(AGDA) -i $(agda-path) PropertiesER.agda
	$(AGDA) -i $(agda-path) ProofSpecificationER.agda

type-checking-all : type-checking-ER type-checking

test : type-checking-all conjectures

publish :
	rm -r -f html/
	$(AGDA) --html -i $(agda-path) ProofSpecification.agda
	scp -P $(port) -r html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp

