# Tunneling connection
host_dir = asicard@localhost:./tmp/GCD/
port = 2024

agda-path = /home/asr/code/phd/LTC/LTC-ATP/

conjectures :
	./test-conjectures.bash

only-type-checking :
	agda -i $(agda-path) ProofSpecificationER.agda
	agda -i $(agda-path) ProofSpecification.agda

test : only-type-checking conjectures

publish :
	rm -r -f html/
	agda --html -i $(agda-path) ProofSpecification.agda
	scp -P $(port) -r html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
